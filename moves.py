from copy import deepcopy
from nodes import ForallNode, ExistsNode, ImpliesNode, IffNode, VarNode, EqNode, \
     NeqNode, LtNode, GtNode, LeqNode, GeqNode, OrNode, AndNode, NotNode, \
     FnNode, LRNode, ConstNode, LeafNode, TupleNode
from type import FnType, TupleType
from unification import unify, subst
from editor import edit
from parser import to_ast
from interface import nchars_to_chars

class TargetNode:
    def __init__(self, num, andlist=[]):
        self.num = num # which target this node corresponds to
        self.proved = False # start in unproved state
        self.andlist = andlist # a list of targets that would prove this target
        self.deps = [] # other targets that the current proofs of this one depends on

    def __str__(self):
        if not self.andlist:
            return "("+str(self.num)+")"
        else:
            return "("+str(self.num)+", ["+", ".join([str(j) for j in self.andlist])+"])"

def metavars_used(tree):
    used = []

    def search(tree):
        if tree == None:
            return
        elif isinstance(tree, LRNode):
            search(tree.left)
            search(tree.right)
        elif isinstance(tree, VarNode):
            if tree.is_metavar:
                name = tree.name
                if name not in used:
                    used.append(name)
        elif isinstanced(tree, FnNode):
            if tree.is_metavar:
                name = tree.name
                if name not in used:
                    used.append(name)
            for v in tree.args:
                search(v)
        return

    search(tree)
    return used

def targets_proved(screen, tl, ttree):
    hyps = tl.tlist1.data
    tars = tl.tlist2.data
    
    def check(ttree):
        if ttree.proved:
            return True
        if ttree.andlist:
            proved = True
            for Q in ttree.andlist:
                proved = check(Q) and proved # and is short circuiting
            ttree.proved = proved
            if not ttree.proved:
                S = set(ttree.andlist[0].deps)
                for i in range(1, len(ttree.andlist)):
                    S = S.intersection(ttree.andlist[i].deps)
                ttree.deps = list(S)
                if ttree.num in ttree.deps:
                    ttree.proved = True
        if not ttree.proved and ttree.num != -1:
            for i in range(0, len(hyps)):
                P = hyps[i]
                dep = tl.tlist1.dependency(i)
                if dep not in ttree.deps: # if we didn't already prove with this dep
                    unifies, assign = unify(P, tars[ttree.num])
                    if unifies:
                        if dep == -1:
                            ttree.proved = True
                            break
                        else:
                            ttree.deps.append(dep)
        return ttree.proved

    return check(ttree)

def mark_proved(ttree, n):
    if ttree.num == n:
        ttree.proved = True
        return True
    for P in ttree.andlist:
        if mark_proved(P, n):
            return True
    return False

def deps_compatible(ttree, d1, d2):
    def find(ttree, d1):
        if ttree.num == d1:
            return ttree
        for P in ttree.andlist:
            t = find(P, d1)
            if t:
                return t
        return None

    root = find(ttree, d2)
    if find(root, d1):
        return True
    else:
        return False

def check_contradictions(screen, tl, n, ttree):
    tlist1 = tl.tlist1.data
    for i in range(n, len(tlist1)):
        d1 = tl.tlist1.dependency(i)
        tree1 = complement_tree(tlist1[i])
        for j in range(0, i):
            d2 = tl.tlist1.dependency(j)
            if d1 < 0 or d2 < 0:
                tree2 = tlist1[j]
                unifies, assign = unify(tree1, tree2)
                if unifies: # we found a contradiction
                    if d1 >= 0:
                        mark_proved(ttree, d1)
                    else:
                        mark_proved(ttree, d2)
            elif d1 >= 0 and d2 >= 0:
                if deps_compatible(ttree, d1, d2):
                    tree2 = tlist1[j]
                    unifies, assign = unify(tree1, tree2)
                    if unifies: # we found a contradiction
                        mark_proved(ttree, d1)
                elif deps_compatible(ttree, d2, d1):
                    tree2 = tlist1[j]
                    unifies, assign = unify(tree1, tree2)
                    if unifies: # we found a contradiction
                        mark_proved(ttree, d2)
    return len(tlist1)

def relabel_varname(name, var_dict):
    if name in var_dict:
        subscript = var_dict[name] + 1
    else:
        subscript = 0
    var_dict[name] = subscript
    return name+'_'+chr(48+subscript)

def relabel(tree, tldict):
    vars_dict = dict()
    
    def process(tree):
        if tree == None:
            return
        elif isinstance(tree, VarNode):
            if tree.name in vars_dict:
                tree.name = vars_dict[tree.name]
        elif isinstance(tree, LRNode):
            process(tree.left)
            process(tree.right)
        elif isinstance(tree, FnNode) or isinstance(tree, TupleNode):
            for v in tree.args:
                process(v)
        
    t = tree
    while isinstance(t, ForallNode) or isinstance(t, ExistsNode):
        name = t.var.name
        new_name = relabel_varname(name, tldict)
        vars_dict[name] = new_name
        t.var.name = new_name
        t = t.left

    process(t)
    return tree

def select_substring(screen, tl):
    window = screen.win1
    pad = screen.pad1
    tlist = tl.tlist1
    window.refresh()
    hyp = True

    screen.status("Select start of substring to apply equality to and press Enter")
    window.refresh()

    while True:
        c = screen.stdscr.getkey()
        if c == 'KEY_UP':
            if pad.scroll_line > 0 or pad.cursor_line > 0:
                pad.cursor_up()
                pad.refresh()
        elif c == 'KEY_DOWN':
            if pad.scroll_line + pad.cursor_line < tlist.len():
                pad.cursor_down()
                pad.refresh()
        elif c == 'KEY_RIGHT':
            pad.cursor_right()
            pad.refresh()
        elif c == 'KEY_LEFT':
            pad.cursor_left()
            pad.refresh()
        elif c == '\t': # TAB = switch hypotheses/targets, forward/backward
            pad = screen.pad2 if pad == screen.pad1 else screen.pad1
            window = screen.win2 if window == screen.win1 else screen.win1
            tlist = tl.tlist2 if tlist == tl.tlist1 else tl.tlist1
            hyp = not hyp
            pad.refresh()
        elif c == '\x1b': # ESC = cancel
            screen.status("")
            return True, 0, 0, 0
        elif c == '\n':
            line = pad.scroll_line + pad.cursor_line
            pad.rev1 = pad.scroll_char + nchars_to_chars(pad.pad[line], \
                              pad.scroll_char, pad.cursor_char)
            pad.rev2 = pad.rev1
            break
        else:
            screen.status("")
            return True, 0, 0, 0
    screen.status("Select end of substring to apply equality to and press Enter")
    window.refresh()
    while True:
        c = screen.stdscr.getkey()
        if c == 'KEY_RIGHT':
            pad.cursor_right()
            line = pad.scroll_line + pad.cursor_line
            pad.rev2 = pad.scroll_char + nchars_to_chars(pad.pad[line], \
                              pad.scroll_char, pad.cursor_char)
            pad.refresh()
        elif c == 'KEY_LEFT':
            pad.cursor_left()
            line = pad.scroll_line + pad.cursor_line
            char = pad.scroll_char + nchars_to_chars(pad.pad[line], \
                              pad.scroll_char, pad.cursor_char)
            pad.rev2 = max(char, pad.rev1)
            pad.refresh()
        elif c == '\x1b': # ESC = cancel
            pad.rev1 = 0
            pad.rev2 = 0
            pad.refresh()
            screen.status("")
            return True, 0, 0, 0
        elif c == '\n':
            rev1 = pad.rev1
            rev2 = pad.rev2
            pad.rev1 = 0
            pad.rev2 = 0
            pad.refresh()
            screen.status("")
            return hyp, pad.cursor_line + pad.scroll_line, rev1, rev2
        else:
            pad.rev1 = 0
            pad.rev2 = 0
            pad.refresh()
            screen.status("")
            return True, 0, 0, 0 

def trim_spaces(string, start, end):
    while start <= end and string[start] == ' ':
        start += 1
    while end > start and string[end - 1] == ' ':
        end -= 1
    return start, string[start:end]

def find_all(string, substring):
    start = 0
    res = []
    n = len(substring)
    while True:
        start = string.find(substring, start)
        if start == -1:
            return res
        res.append(start)
        start += n

def apply_equality(screen, tree, string, n, subst, occurred=-1):
    occur = occurred
    found = False
    if tree == None:
        return False, None, occur
    if str(tree) == string: # we found an occurrence
        occur += 1
        if occur == n: # we found the right occurrence
            unifies, assign = unify(subst.left, tree)
            if not unifies:
                return False, tree, n # does not unify, bogus selection
            return True, substitute(deepcopy(subst.right), assign), n
    if isinstance(tree, LRNode):
        found, tree.left, occur = apply_equality(screen, tree.left, string, n, subst, occur)
        if not found:
            found, tree.right, occur = apply_equality(screen, tree.right, string, n, subst, occur)
        return found, tree, occur
    elif isinstance(tree, LeafNode):
        return found, tree, occur
    # TODO : deal with FnNode and friends
    raise Exception("Node not dealt with")

def equality(screen, tl):
    screen.save_state()
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    screen.status("Select equality")
    hyp1, line1 = select_hypothesis(screen, tl, False)
    if line1 == -1: # Cancelled
        screen.status("")
        screen.restore_state()
        screen.focus.refresh()
        return
    tree1 = tlist1.data[line1]
    if not isinstance(tree1, EqNode): # not an equality
        screen.dialog("Not an equality. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return 
    hyp2, line2, start, end = select_substring(screen, tl)
    screen.status("")
    if start == end: # canceled
        screen.restore_state()
        screen.focus.refresh()
        return 
    if hyp2:
        sub_pad = screen.pad1
        sub_tlist = tlist1
    else:
        sub_pad = screen.pad2
        sub_tlist = tlist2
    string = sub_pad.pad[line2]
    start, sub_string = trim_spaces(string, start, end)
    if sub_string == '':
        screen.dialog("Empty subexpression. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return
    idx = find_all(string, sub_string)
    n = idx.index(start) # which occurence of substring do we want (0-indexed)
    found, tree, occur = apply_equality(screen, sub_tlist.data[line2], sub_string, n, tree1)
    if not found:
        screen.dialog("Equality cannot be applied. Press Enter to continue")
        screen.restore_state()
        screen.focus.refresh()
        return
    else:
        sub_tlist.data[line2] = tree
        sub_pad.pad[line2] = str(sub_tlist.data[line2])
        sub_pad.refresh()
    screen.restore_state()
    screen.focus.refresh()
    
def new_result(screen, tl):
    tlist0 = tl.tlist0
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    pad0 = screen.pad0
    pad1 = screen.pad1
    pad2 = screen.pad2
    tlist0.data = []
    pad0.pad[0] = ''
    n = len(tlist1.data)
    for i in range(0, n):
        del tlist1.data[n - i - 1]
        pad1.pad[i] = ''
    tlist1.line = 0
    n = len(tlist2.data)
    for i in range(0, n):
        del tlist2.data[n - i - 1]
        pad2.pad[i] = ''
    tlist2.line = 0
    pad1.scoll_line = 0
    pad1.cursor_line = 0
    pad2.scroll_line = 0
    pad2.cursor_line = 0
    pad2.refresh()
    pad1.refresh()
    pad0.refresh()
    screen.focus = screen.pad0
    tl.focus = tl.tlist0

canonical_numtypes = { "\\N" : "\\mathbb{N}",
                       "\\Z" : "\\mathbb{Z}",
                       "\\Q" : "\\mathbb{Q}",
                       "\\R" : "\\mathbb{R}",
                       "\\C" : "\\mathbb{C}"}

def tags_to_list(tags):
    return tags[6:].split(" ")

def canonicalise_tags(tags):
    taglist = tags_to_list(tags)
    for i in range(0, len(taglist)):
        tag = taglist[i][1:]
        if tag in canonical_numtypes:
            taglist[i] = "#"+canonical_numtypes[tag]
    return "Tags: "+' '.join(taglist)

def filter_titles(titles, c):
    titles2 = []
    for (line, v) in titles:
        if v[0] == c or v[0] == c.upper():
            titles2.append((line, v))
    return titles2

def library_import(screen, tl):
    tags = edit(screen, "Tags: ", 6)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with type shorthands
    taglist = tags_to_list(tags)
    library = open("library.dat", "r")
    filtered_titles = []
    title = library.readline()
    while title: # check for EOF
        libtaglist = tags_to_list(library.readline()[0:-1])
        if all(elem in libtaglist for elem in taglist):
            filtered_titles.append((library.tell(), title[7:-1]))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    filtered_titles2 = deepcopy(filtered_titles)
    i = 0
    if filtered_titles:
        screen.status(filtered_titles2[i][1])
        while True:
            c = screen.stdscr.getkey()
            if c == 'KEY_DOWN' and i < len(filtered_titles2) - 1:
                i += 1
                screen.status(filtered_titles2[i][1])
            elif c == 'KEY_UP' and i > 0:
                i -= 1
                screen.status(filtered_titles2[i][1])
            elif c.isalpha():
                filtered_titles2 = filter_titles(filtered_titles, c)
                i = 0
                if filtered_titles2:
                    screen.status(filtered_titles2[i][1])
            elif c == '\n':
                screen.status('')
                screen.focus.refresh()
                break
            else:
                library.close()
                screen.status('')
                screen.focus.refresh()
                return
        filepos = filtered_titles2[i][0]
        library.seek(filepos)
        fstr = library.readline()
        hyps = []
        tars = []
        if fstr != '------------------------------\n':
            tree = to_ast(screen, fstr[0:-1])
            t = tree
            while t.left:
                t = t.left
            library.readline()
            fstr = library.readline()
            while fstr != '------------------------------\n':
                hyps.append(to_ast(screen, fstr[0:-1]))
                fstr = library.readline()
            fstr = library.readline()
            while fstr != '\n':
                tars.append(to_ast(screen, fstr[0:-1]))
                fstr = library.readline()
            if hyps:
                jhyps = hyps[0]
                for node in hyps[1:]:
                    jhyps = AndNode(jhyps, node)
            jtars = tars[0]
            for i in tars[1:]:
                jtars = AndNode(jtars, i)
            if hyps:
                t.left = ImpliesNode(jhyps, jtars)
            else:
                t.left = jtars
        else:
            library.readline()
            library.readline()
            fstr = library.readline()
            while fstr != '\n':
                tars.append(to_ast(screen, fstr[0:-1]))
                fstr = library.readline()
            tree = tars[0]
            for i in tars[1:]:
                tree = AndNode(tree, i)
        tlist1 = tl.tlist1.data
        pad1 = screen.pad1.pad
        stmt = relabel(tree, tl.vars)
        append_tree(pad1, tlist1, stmt)
        screen.pad1.refresh()
        screen.focus.refresh()
    library.close()

def library_load(screen, tl):
    tags = edit(screen, "Tags: ", 6)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with type shorthands
    taglist = tags_to_list(tags)
    library = open("library.dat", "r")
    filtered_titles = []
    title = library.readline()
    while title: # check for EOF
        libtaglist = tags_to_list(library.readline()[0:-1])
        if all(elem in libtaglist for elem in taglist):
            filtered_titles.append((library.tell(), title[7:-1]))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    filtered_titles2 = deepcopy(filtered_titles)
    i = 0
    if filtered_titles:
        screen.status(filtered_titles2[i][1])
        while True:
            c = screen.stdscr.getkey()
            if c == 'KEY_DOWN' and i < len(filtered_titles2) - 1:
                i += 1
                screen.status(filtered_titles2[i][1])
            elif c == 'KEY_UP' and i > 0:
                i -= 1
                screen.status(filtered_titles2[i][1])
            elif c.isalpha():
                filtered_titles2 = filter_titles(filtered_titles, c)
                i = 0
                if filtered_titles2:
                    screen.status(filtered_titles2[i][1])
            elif c == '\n':
                screen.status('')
                screen.focus.refresh()
                break
            else:
                library.close()
                screen.status('')
                screen.focus.refresh()
                return
        filepos = filtered_titles2[i][0]
        library.seek(filepos)
        tlist0 = tl.tlist0.data
        pad0 = screen.pad0.pad
        tlist1 = tl.tlist1.data
        pad1 = screen.pad1.pad
        tlist2 = tl.tlist2.data
        pad2 = screen.pad2.pad
        fstr = library.readline()
        if fstr != '------------------------------\n':
            stmt = to_ast(screen, fstr[0:-1])
            append_tree(pad0, tlist0, stmt)
            screen.pad0.refresh()
            library.readline()
            fstr = library.readline()
            while fstr != '------------------------------\n':
                stmt = to_ast(screen, fstr[0:-1])
                append_tree(pad1, tlist1, stmt)
                screen.pad1.refresh()
                fstr = library.readline()
            fstr = library.readline()
            while fstr != '\n':
                stmt = to_ast(screen, fstr[0:-1])
                append_tree(pad2, tlist2, stmt)
                screen.pad2.refresh()
                fstr = library.readline()
        else:
            library.readline()
            library.readline()
            fstr = library.readline()
            while fstr != '\n':
                stmt = to_ast(screen, fstr[0:-1])
                append_tree(pad2, tlist2, stmt)
                screen.pad2.refresh()
                fstr = library.readline()
        screen.focus.refresh()
    library.close()

def library_export(screen, tl):
    title = edit(screen, "Title: ", 7)
    if title == None:
        return
    tags = edit(screen, "Tags: ", 6)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with type shorthands
    library = open("library.dat", "a")
    library.write(title+"\n")
    library.write(tags+"\n")
    tlist0 = tl.tlist0.data
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    qz_written = False
    if tlist0:
        library.write(repr(tlist0[0]))
        qz_written = True
    for hyp in tlist1:
        while isinstance(hyp, ExistsNode):
            if qz_written:
                library.write(" ")
            library.write(repr(ExistsNode(hyp.var, None)))
            hyp = hyp.left
            qz_written = True
    for tar in tlist2:
        while isinstance(tar, ForallNode):
            if qz_written:
                library.write(" ")
            library.write(repr(ForallNode(tar.var, None)))
            tar = tar.left
            qz_written = True
    if qz_written:
        library.write("\n")
    library.write("------------------------------\n")
    for hyp in tlist1:
        while isinstance(hyp, ExistsNode):
            hyp = hyp.left
        library.write(repr(hyp)+"\n")
    library.write("------------------------------\n")
    for tar in tlist2:
        while isinstance(tar, ForallNode):
            tar = tar.left
        library.write(repr(tar)+"\n")
    library.write("\n")
    library.close()
    screen.focus.refresh()

def complement_tree(tree):
    
    def complement(tree):
        if isinstance(tree, ForallNode):
            return ExistsNode(tree.var, complement(tree.left))
        elif isinstance(tree, ExistsNode):
            return ForallNode(tree.var, complement(tree.left))
        elif isinstance(tree, EqNode):
            return NeqNode(tree.left, tree.right)
        elif isinstance(tree, NeqNode):
            return EqNode(tree.left, tree.right)
        elif isinstance(tree, LtNode):
            return GeqNode(tree.left, tree.right)
        elif isinstance(tree, GtNode):
            return LeqNode(tree.left, tree.right)
        elif isinstance(tree, LeqNode):
            return GtNode(tree.left, tree.right)
        elif isinstance(tree, GeqNode):
            return LtNode(tree.left, tree.right)
        elif isinstance(tree, AndNode):
            return OrNode(complement(tree.left), complement(tree.right))
        elif isinstance(tree, OrNode):
            return AndNode(complement(tree.left), complement(tree.right))
        elif isinstance(tree, NotNode):
            return tree.left
        else:
            return NotNode(tree)

    return complement(deepcopy(tree))

def select_hypothesis(screen, tl, second):
    window = screen.win1
    pad = screen.pad1
    tlist = tl.tlist1
    window.refresh()
    forward = True

    while True:
        c = screen.stdscr.getkey()
        if c == 'KEY_UP':
            if pad.scroll_line > 0 or pad.cursor_line > 0:
                pad.cursor_up()
                pad.refresh()
        elif c == 'KEY_DOWN':
            if pad.scroll_line + pad.cursor_line < tlist.len():
                pad.cursor_down()
                pad.refresh()
        elif second and c == '\t': # TAB = switch hypotheses/targets, forward/backward
            pad = screen.pad2 if forward else screen.pad1
            window = screen.win2 if forward else screen.win1
            tlist = tl.tlist2 if forward else tl.tlist1
            forward = not forward
            pad.refresh()
        elif c == '\x1b': # ESC = cancel
            return True, -1
        elif c == '\n':
            return forward, pad.scroll_line + pad.cursor_line
        else:
            return True, -1

def unquantify(tree):
    mv = []
    while isinstance(tree, ForallNode):
        mv.append(tree.var.name)
        tree = tree.left
    return skolemize_statement(tree, [], [], [], mv, False)

def target_compatible(ttree, tlist1, d1, j, forward):
    if forward:
        d2 = tlist1.dependency(j)
    else:
        d2 = j
    if d1 < d2:
        d1, d2 = d2, d1
    if d1 >= 0 and d2 >= 0 and not deps_compatible(ttree, d1, d2):
       return None
    return d1

def modus_ponens(screen, tl, ttree):
    screen.save_state()
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    screen.status("Select implication")
    forward, line1 = select_hypothesis(screen, tl, False)
    if line1 == -1: # Cancelled
        screen.status("")
        screen.restore_state()
        screen.focus.refresh()
        return
    tree1 = tlist1.data[line1]
    tree1 = unquantify(deepcopy(tree1)) # remove quantifiers by taking temporary metavars
    if not isinstance(tree1, ImpliesNode) and not isinstance(tree1, IffNode): # no implication after quantifiers
        screen.dialog("Not an implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return
    screen.status("Select predicate")
    forward, line2 = select_hypothesis(screen, tl, True)
    screen.status("")
    if line2 == -1: # Cancelled
        screen.status("")
        screen.restore_state()
        screen.focus.refresh()
        return
    dep = tlist1.dependency(line1)
    dep = target_compatible(ttree, tlist1, dep, line2, forward)
    if dep == None:
        screen.dialog("Not target compatible. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return
    qP1 = tree1.left if forward else tree1.right
    tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
    t = qP1
    n = 1
    while isinstance(t, AndNode):
        t = t.left
        n += 1
    for i in range(1, n): # get remaining predicates
        screen.status("Select predicate "+str(i+1))
        forward2, line2 = select_hypothesis(screen, tl, True)
        screen.status("")
        if line2 == -1: # Cancelled
            screen.status("")
            screen.restore_state()
            screen.focus.refresh()
            return
        if forward2 != forward:
            screen.dialog("Predicates must be all hypotheses or all targets. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
        dep = target_compatible(ttree, tlist1, dep, line2, forward)
        if dep == None:
            screen.dialog("Not target compatible. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
        new_tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
        tree2 = AndNode(tree2, new_tree2)
    qP2 = tree2
    unifies, assign = unify(qP1, qP2)
    if not unifies:
        screen.dialog("Predicate does not match implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return # does not unify, bogus selection
    if forward:
        stmt = substitute(deepcopy(tree1.right), assign)
        stmt = relabel(stmt, tl.vars)
        append_tree(screen.pad1, tlist1.data, stmt)
        tlist1.dep[len(tlist1.data) - 1] = dep
    else:
        stmt = substitute(deepcopy(tree1.left), assign)
        stmt = relabel(stmt, tl.vars)
        append_tree(screen.pad2, tlist2.data, stmt)
        add_descendant(ttree, line2, len(tlist2.data) - 1)
    # update windows
    tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
    tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def modus_tollens(screen, tl, ttree):
    screen.save_state()
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    screen.status("Select implication")
    forward, line1 = select_hypothesis(screen, tl, False)
    if line1 == -1: # Cancelled
        screen.status("")
        screen.restore_state()
        screen.focus.refresh()
        return
    tree1 = tlist1.data[line1]
    tree1 = unquantify(deepcopy(tree1))
    if not isinstance(tree1, ImpliesNode) and not isinstance(tree1, IffNode): # no implication after quantifiers
        screen.dialog("Not an implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return 
    screen.status("Select predicate")
    forward, line2 = select_hypothesis(screen, tl, True)
    screen.status("")
    if line2 == -1: # Cancelled
        screen.status("")
        screen.restore_state()
        screen.focus.refresh()
        return
    dep = tlist1.dependency(line1)
    dep = target_compatible(ttree, tlist1, dep, line2, forward)
    if dep == None:
        screen.dialog("Not target compatible. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return
    tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
    qP1 = complement_tree(tree1.right) if forward else \
          complement_tree(tree1.left)
    t1 = qP1
    n = 1 # number of hypotheses/targets in conjunction
    while isinstance(t1, AndNode):
        t1 = t1.left
        n += 1
    for i in range(1, n): # get remaining predicates
        screen.status("Select predicate "+str(i+1))
        forward2, line2 = select_hypothesis(screen, tl, True)
        screen.status("")
        if line2 == -1: # Cancelled
            screen.status("")
            screen.restore_state()
            screen.focus.refresh()
            return
        if forward2 != forward:
            screen.dialog("Predicates must be all hypotheses or all targets. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
        dep = target_compatible(ttree, tlist1, dep, line2, forward)
        if dep == None:
            screen.dialog("Not target compatible. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
        new_tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
        tree2 = AndNode(tree2, new_tree2)
    qP2 = tree2
    unifies, assign = unify(qP1, qP2)
    if not unifies:
        screen.dialog("Predicate does not match implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return # does not unify, bogus selection
    if forward:
        stmt = complement_tree(substitute(deepcopy(tree1.left), assign))
        stmt = relabel(stmt, tl.vars)
        append_tree(screen.pad1, tlist1.data, stmt)
        tlist1.dep[len(tlist1.data) - 1] = dep
    else:
        stmt = complement_tree(substitute(deepcopy(tree1.right), assign))
        stmt = relabel(stmt, tl.vars)
        append_tree(screen.pad2, tlist2.data, stmt)
        add_descendant(ttree, line2, len(tlist2.data) - 1)
    # update windows
    tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
    tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def substitute(tree, assign):
   for (var, val) in assign:
       tree = subst(tree, var, val)
   return tree

def append_tree(pad, tl, stmt):
    n = len(tl)
    tl.append(stmt)
    pad[n] = str(tl[n])
            
def replace_tree(pad, tl, i, stmt):
    tl[i] = stmt
    pad[i] = str(tl[i])

def add_sibling(ttree, i, j):
    for P in ttree.andlist:
        if P.num == i:
            ttree.andlist.append(TargetNode(j))
            return True
    for P in ttree.andlist:
        if add_sibling(P, i, j):
            return True
    return False

def add_descendant(ttree, i, j):
    if ttree.num == i:
        ttree.andlist = [TargetNode(j)]
        return True
    for P in ttree.andlist:
        if add_descendant(P, i, j):
            return True
    return False

def cleanup(screen, tl, ttree):
    tl0 = tl.tlist0.data # quantifier zone
    tl1 = tl.tlist1.data # hypotheses
    tl2 = tl.tlist2.data # targets
    deps = []
    sk = []
    qz = []
    mv = []
    if tl0:
        sq, deps, sk = skolemize_quantifiers(tl0[0], deps, sk)
        if sq:
            tl.tlist0.data[0] = sq
            screen.pad0[0] = str(tl.tlist0.data[0])
        else:
            del tl.tlist0.data[0]
            screen.pad0[0] = ''

    d = len(deps)
    s = len(sk)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()

    hyps_done = False
    tars_done = False
    i = 0
    j = 0
    while not hyps_done or not tars_done:
        if not hyps_done:
            hyps_done = True
            while i < len(tl1):
                tl1[i] = skolemize_statement(tl1[i], deps, sk, qz, mv, False)
                rollback()
                t = tl1[i]
                if isinstance(t, ExistsNode) or isinstance(t, ForallNode):
                    while isinstance(t, ExistsNode) or isinstance(t, ForallNode) \
                           and not isinstance(t.left, OrNode):
                        t = t.left
                    if isinstance(t.left, OrNode):
                        t.left = ImpliesNode(complement_tree(t.left.left), t.left.right)
                        if isinstance(t.left.left, NotNode) and isinstance(t.left.right, NotNode):
                            temp = t.left.left.left
                            t.left.left = t.left.right.left
                            t.left.right = temp
                        screen.pad1[i] = str(tl1[i])
                if isinstance(tl1[i], OrNode):
                    # First check we don't have P \vee P
                    unifies, assign = unify(tl1[i].left, tl1[i].right)
                    if unifies and not assign:
                        replace_tree(screen.pad1, tl1, i, tl1[i].left)
                    else:
                        stmt = ImpliesNode(complement_tree(tl1[i].left), tl1[i].right)
                        if isinstance(stmt.left, NotNode) and isinstance(stmt.right, NotNode):
                            temp = stmt.left.left
                            stmt.left = stmt.right.left
                            stmt.right = temp
                        replace_tree(screen.pad1, tl1, i, stmt)
                if isinstance(tl1[i], IffNode):
                    tl1[i] = ImpliesNode(tl1[i].left, tl1[i].right)
                    impl = ImpliesNode(deepcopy(tl1[i].right), deepcopy(tl1[i].left))
                    append_tree(screen.pad1, tl1, impl)
                    tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                while isinstance(tl1[i], AndNode):
                    # First check we don't have P \vee P
                    unifies, assign = unify(tl1[i].left, tl1[i].right)
                    if unifies and not assign:
                        replace_tree(screen.pad1, tl1, i, tl1[i].left)
                    else:
                        append_tree(screen.pad1, tl1, tl1[i].right)
                        replace_tree(screen.pad1, tl1, i, tl1[i].left)
                        tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                if isinstance(tl1[i], NotNode) and isinstance(tl1[i].left, ImpliesNode):
                    append_tree(screen.pad1, tl1, complement_tree(tl1[i].left.right))
                    replace_tree(screen.pad1, tl1, i, tl1[i].left.left)
                    tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                if isinstance(tl1[i], ImpliesNode) and isinstance(tl1[i].left, OrNode):
                    var1 = metavars_used(tl1[i].left.left)
                    var2 = metavars_used(tl1[i].left.right)
                    var = metavars_used(tl1[i].right)
                    # make sure no additional metavars are introduced
                    if set(var).issubset(var1) and set(var).issubset(var2):
                        P = tl1[i].left.left
                        Q = tl1[i].left.right
                        R = tl1[i].right
                        append_tree(screen.pad1, tl1, ImpliesNode(Q, R))
                        replace_tree(screen.pad1, tl1, i, ImpliesNode(P, R))
                        tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                if isinstance(tl1[i], ImpliesNode) and isinstance(tl1[i].right, AndNode):
                    stmt = ImpliesNode(deepcopy(tl1[i].left), tl1[i].right.left)
                    append_tree(screen.pad1, tl1, stmt)
                    stmt = ImpliesNode(tl1[i].left, tl1[i].right.right)
                    replace_tree(screen.pad1, tl1, i, stmt)
                    tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                screen.pad1[i] = str(tl1[i])
                i += 1
        if not tars_done:
            tars_done = True
            while j < len(tl2):
                tl2[j] = skolemize_statement(tl2[j], deps, sk, qz, mv, True)
                rollback()
                if isinstance(tl2[j], OrNode):
                    append_tree(screen.pad1, tl1, complement_tree(tl2[j].left))
                    hyps_done = False
                    replace_tree(screen.pad2, tl2, j, tl2[j].right)
                    tl.tlist1.dep[len(tl1) - 1] = j
                if isinstance(tl2[j], ImpliesNode):
                    left = relabel(tl2[j].left, tl.vars)
                    append_tree(screen.pad1, tl1, left)
                    hyps_done = False
                    right = relabel(tl2[j].right, tl.vars)
                    replace_tree(screen.pad2, tl2, j, right)
                    tl.tlist1.dep[len(tl1) - 1] = j
                while isinstance(tl2[j], AndNode):
                    # First check we don't have P \wedge P
                    unifies, assign = unify(tl2[j].left, tl2[j].right)
                    if unifies and not assign:
                        replace_tree(screen.pad1, tl2, j, tl2[j].left)
                    else:
                        append_tree(screen.pad2, tl2, tl2[j].right)
                        replace_tree(screen.pad2, tl2, j, tl2[j].left)
                        add_sibling(ttree, j, len(tl2) - 1)
                if isinstance(tl2[j], NotNode) and isinstance(tl2[j].left, ImpliesNode):
                    append_tree(screen.pad2, tl2, complement_tree(tl2[j].left.right))
                    replace_tree(screen.pad2, tl2, j, tl2[j].left.left)
                    add_sibling(ttree, j, len(tl2) - 1)
                screen.pad2[j] = str(tl2[j])
                j += 1
    
    if qz:
        if tl0:
            t = tl0[0]
            while t.left:
                t = t.left
            r = range(0, len(qz))
        else:
            tl0.append(qz[0])
            t = qz[0]
            r = range(1, len(qz))
        for i in r:
            t.left = qz[i]
            t = t.left
        t.left = None
        screen.pad0[0] = str(tl.tlist0.data[0])

    screen.focus.cursor_adjust()
    screen.pad0.refresh()
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def skolemize_quantifiers(tree, deps, sk):
    if isinstance(tree, ExistsNode):
        sk.append((tree.var.name, len(deps)))
        deps.append(tree.var)
        return skolemize_quantifiers(tree.left, deps, sk)
    elif isinstance(tree, ForallNode):
        deps.append(tree.var)
        tree.left, deps, sk = skolemize_quantifiers(tree.left, deps, sk)
        return tree, deps, sk
    else:
        return tree, deps, sk

def skolemize_statement(tree, deps, sk, qz, mv, positive, blocked=False):
    d = len(deps)
    s = len(sk)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()
 
    if isinstance(tree, OrNode):
        tree.left = skolemize_statement(tree.left, deps, sk, qz, mv, positive, True)
        tree.right = skolemize_statement(tree.right, deps, sk, qz, mv, positive, True)
        return tree
    elif isinstance(tree, ForallNode):
        is_blocked = blocked
        if not blocked:
            if positive:
                deps.append(tree.var)
                qz.append(tree)
            else:
                if not isinstance(tree.left, ImpliesNode) and not isinstance(tree.left, OrNode):
                    tree.var.is_metavar = True
                    deps.append(tree.var)
                    mv.append(tree.var.name)
                    qz.append(ConstNode(tree.var, None))
                else:
                    is_blocked = True
        rollback()
        tree.left = skolemize_statement(tree.left, deps, sk, qz, mv, positive, is_blocked)
        return tree.left if not is_blocked else tree    
    elif isinstance(tree, ExistsNode):
        is_blocked = blocked
        if not blocked:
            sk.append((tree.var.name, len(deps)))
            domain_types = [v.var.type if isinstance(v, ForallNode) else v.type for v in deps]
            if len(domain_types) > 1:
                fn_type = FnType(TupleType(domain_types), tree.var.type)
            elif len(domain_types) == 1:
                fn_type = FnType(domain_types[0], tree.var.type)
            else:
                fn_type = FnType(None, tree.var.type)
            if positive:
                if not blocked:
                    tree.var.is_metavar = True
                    mv.append(tree.var.name)
                if not isinstance(tree.left, ImpliesNode) and not isinstance(tree.left, OrNode):
                    domain_types = [v.var.type if isinstance(v, ForallNode) else v.type for v in deps]
                    qz.append(ConstNode(VarNode(tree.var.name, fn_type, True), None))
                else:
                    is_blocked = True
            else:
                #deps.append(tree.var) # not needed? depends on all same things?
                qz.append(ForallNode(VarNode(tree.var.name, fn_type, False), None))
        tree.left = skolemize_statement(tree.left, deps, sk, qz, mv, positive, is_blocked)
        rollback()
        return tree.left if not blocked else tree
    elif isinstance(tree, IffNode) or isinstance(tree, ImpliesNode):
        t = tree
        while isinstance(t.left, ForallNode) or isinstance(t.left, ExistsNode):
            t = t.left
        t.left = skolemize_statement(t.left, deps, sk, qz, mv, not positive, blocked)
        if not isinstance(tree.right, ForallNode) and not isinstance(tree.right, ExistsNode):
            tree.right = skolemize_statement(tree.right, deps, sk, qz, mv, positive)
        else:
            t = tree.right
            while isinstance(t.left, ForallNode) or isinstance(t.left, ExistsNode):
                t = t.left
            t.left = skolemize_statement(t.left, deps, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, LRNode):
        tree.left = skolemize_statement(tree.left, deps, sk, qz, mv, positive, blocked)
        tree.right = skolemize_statement(tree.right, deps, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, VarNode):
        is_meta = False
        if tree.name in mv:
            is_meta = True
            tree.is_metavar = True
        n = skolem_deps(tree.name, sk)
        if n == -1: # not a skolem variable
            return tree
        else:
            fn_args = [VarNode(deps[i].name, deps[i].type, deps[i].is_metavar) \
                    for i in range(0, n)]
            fn = FnNode(tree.name, fn_args)
            fn.is_skolem = True
            if is_meta:
                fn.is_metavar = True
            return fn
    elif isinstance(tree, FnNode) or isinstance(tree, TupleNode):
        for i in range(0, len(tree.args)):
            tree.args[i] = skolemize_statement(tree.args[i], deps, sk, qz, mv, positive, blocked)
            rollback()
        return tree
    else:
        return tree
        
def skolem_deps(name, sk):
    for (v, n) in sk:
        if v == name:
            return n
    return -1
