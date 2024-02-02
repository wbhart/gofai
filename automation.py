from utility import is_implication, get_constants, get_init_vars, list_merge, deps_compatible, \
     TargetNode, update_constraints, process_sorts, append_tree, unquantify, target_compatible, \
     append_quantifiers, relabel, deps_defunct, is_duplicate_upto_metavars, metavars_used, \
     vars_used, max_type_size, complement_tree, sorts_mark, sorts_rollback, is_equality, \
     target_depends, get_constants_qz
from autoparse import parse_consts
from moves import check_targets_proved
from unification import unify, substitute
from nodes import DeadNode, AutoImplNode, AutoEqNode, AutoIffNode, ImpliesNode, AndNode, \
     SymbolNode, NeqNode, ForallNode, EqNode, NotNode, FnApplNode, SubsetneqNode
from tree import TreeList
from interface import nchars_to_chars, iswide_char
from copy import deepcopy
import logic, math

automation_limit     = 1000 # number of lines in hypothesis pane before automation gives up
automation_increment = 300 # number of lines to add next time automation is called

# Mode 0 : backwards reasoning only uses definitions, no metavars are allowed to be introduced in targets
# Mode 1 : backwards reasoning may use any implication, new metavars are allowed to be introduced in targets using definitions
# depth  : search depth on the hypothesis side

try:
    from flask import Flask, render_template
    from flask_socketio import SocketIO, emit
except:
    pass

class SkolemNode:
    def __init__(self, lines):
        self.lines = lines

class AutoData:
    def __init__(self, line, const1, const2, nconst1, nconst2):
        self.line = line # line in the hypothesis or target pane
        self.const1 = const1 # constants on left side of implication or constants in predicate
        self.const2 = const2 # constants on right side of implication
        self.nconst1 = nconst1 # negated constants on left side of implication or constants in predicate
        self.nconst2 = nconst2 # negated constants on right side of implication
        self.deducts = 0 # number of times a deduction has been made from this head
        self.applied = [] # list of heads that have been applied to this
        self.num_mv = 0 # number of metavariables impl will increase or head has been increased
        self.score = 0.0 # score used for heuristic search (lower is better)
        self.impls_done = 0 # number of largest impl checked against this head for application
        self.filepos_done = 0 # largest filepos of theorem checked against this head for application
        self.line_done = 0 # line of theorem at filepos checked against this head
        self.depth = 0 # depth of this head
        self.mv_inc = 0 # number of metavars this implication adds going left to right
        self.nmv_inc = 0 # number of metavars this implication adds going right to left
        self.ltor = True # whether the theorem can be applied left to right
        self.rtol = True # whether the theorem can be applied right to left
        self.defn = False # whether the theorem is a definition

    def __str__(self):
        return str(self.line)

    def __repr__(self):
        return repr(self.line)

class AutoTab:
    def __init__(self, screen, tl):
        tlist0 = tl.tlist0.data
        tlist1 = tl.tlist1.data
        tlist2 = tl.tlist2.data
        self.tl = tl
        self.nhyps = len(tlist1)
        self.ntars = len(tlist2)
        self.vars = get_init_vars(screen, tl, tlist0[0]) if tlist0 else [] # vars in initial tableau
        self.type_consts = get_constants_qz(screen, tl, tlist0[0])
        self.constants = None
        hyp_heads = []
        hyp_impls = []
        tar_heads = []
        max_depth = 0
        max_width = 0
        function_depth = 1 # 1 to allow for is_blah predicates
        for i in range(len(tlist1)):
            v = tlist1[i]
            d, w, f = max_type_size(screen, tl, v)
            max_depth = max(max_depth, d)
            max_width = max(max_width, w)
            function_depth = max(function_depth, f)
            if is_implication(v):
                v, univs = unquantify(screen, v, False)
                c1 = get_constants(screen, tl, v.left)
                c2 = get_constants(screen, tl, v.right)
                nc1 = get_constants(screen, tl, complement_tree(v.left))
                nc2 = get_constants(screen, tl, complement_tree(v.right))
                dat = AutoData(i, c1, c2, nc1, nc2)
                m1 = metavars_used(v.left)
                m2 = metavars_used(v.right)
                mv = filter(lambda x : x not in m1, m2)
                nmv = filter(lambda x : x not in m2, m1)
                dat.score = math.log(d+1)+math.log(w+1)+math.log(f+1)+math.log(len(str(v))+1)+math.log(len(metavars_used(v))+1)
                dat.mv_inc = len(list(mv))
                dat.nmv_inv = len(list(nmv))
                hyp_impls.append(dat)
                dat.num_mv = len(metavars_used(v.right)) - len(metavars_used(v.left))
            else:
                c = get_constants(screen, tl, v)
                nc = get_constants(screen, tl, complement_tree(v))
                ad = AutoData(i, c, None, nc, None)
                ad.score = math.log(d+1)+math.log(w+1)+math.log(f+1)+math.log(len(str(v))+1)+math.log(len(metavars_used(v))+1)
                ad.depth = 0
                insert_sort(screen, hyp_heads, ad)
        for j in range(len(tlist2)):
           v = tlist2[j]
           d, w, f = max_type_size(screen, tl, v)
           max_depth = max(max_depth, d)
           max_width = max(max_width, w)
           function_depth = max(function_depth, f)
           c = get_constants(screen, tl, v)
           nc = get_constants(screen, tl, complement_tree(v))
           tar_heads.append(AutoData(j, c, None, nc, None))
        self.hyp_heads = hyp_heads
        self.hyp_impls = hyp_impls
        self.tar_heads = tar_heads
        self.thms = []
        self.max_depth = max_depth
        self.max_width = max_width
        self.function_depth = function_depth

def compute_direction(atab, dat):
    max_l = -1
    max_r = -1
    for i in range(len(atab.constants)):
        c = atab.constants[i]
        if c in dat.const1:
            max_l = i
        if c in dat.const2:
            max_r = i
    dat.ltor = max_l >= max_r
    max_l = -1
    max_r = -1
    for i in range(len(atab.constants)):
        c = atab.constants[i]
        if c in dat.nconst2:
            max_l = i
        if c in dat.nconst1:
            max_r = i
    dat.rtol = max_l >= max_r
    
def compute_score(screen, tl, dat, is_hyp):
    v = tl.tlist1.data[dat.line] if is_hyp else tl.tlist2.data[dat.line]
    d, w, f = max_type_size(screen, tl, v)
    dat.score = 0
    dat.score += math.log(d+1)
    dat.score += math.log(w+1)
    dat.score += math.log(f+1)
    dat.score += math.log(len(str(v))+1)
    dat.score += math.log(len(metavars_used(v))+1)
    dat.score += math.log(dat.deducts+1)
    dat.score += math.log(dat.depth+1)
    dat.score += math.log(dat.defn+1)

def adjust_score(screen, tl, atab, line, is_hyp):
    is_impl = False
    depth = 0
    if is_hyp:
        found = False
        for k in range(len(atab.hyp_heads)):
            dat = atab.hyp_heads[k]
            if dat.line == line:
                found = True
                depth = dat.depth
                del atab.hyp_heads[k]
                break
        if not found:
            for k in range(len(atab.hyp_impls)):
                dat = atab.hyp_impls[k]
                if dat.line == line:
                    depth = dat.depth
                    is_impl = True
                    del atab.hyp_impls[k]
                    break
    else:
        depth = 0
        for k in range(len(atab.tar_heads)):
            dat = atab.tar_heads[k]
            if dat.line == line:
                del atab.tar_heads[k]
                break

    # add new details
    compute_score(screen, tl, dat, is_hyp)

    if is_hyp:
        if is_impl:
           insert_sort(screen, atab.hyp_impls, dat)
           compute_direction(atab, dat)
        else:
           insert_sort(screen, atab.hyp_heads, dat)
    else:
        insert_sort(screen, atab.tar_heads, dat)

def insert_sort(screen, L, dat):
    """
    Insert an AutoDat node in a list according to score.
    """
    if not L:
        L.append(dat)
    else:
        lo, hi = 0, len(L)

        # Binary search to find the correct insertion point
        while lo < hi:
            mid = (lo + hi) // 2
            # Lower scored objects go earlier in the list
            if L[mid].score < dat.score:
                lo = mid + 1
            else:
                hi = mid

        L.insert(lo, dat)
     
def update_autotab(screen, tl, atab, dirty1, dirty2, interface, depth, defn=False):
    """
    Given an AutoTab data structure and a list of modified/added hypotheses
    (dirty1) and a list of modified/added targets (dirty2), update the data
    in the AutoTab structure to reflect current reality.
    """
    dirty1 = sorted(dirty1)
    dirty2 = sorted(dirty2)
    tlist0 = tl.tlist0.data
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    for i in dirty1:
        deducts = 0
        if i < atab.nhyps: # delete old hypothesis
            j = 0
            while j < len(atab.hyp_heads):
                t = atab.hyp_heads[j]
                if t.line == i:
                    deducts = atab.hyp_heads[j].deducts
                    del atab.hyp_heads[j]
                else:
                    j += 1
            j = 0
            while j < len(atab.hyp_impls):
                t = atab.hyp_impls[j]
                if t.line == i:
                    del atab.hyp_impls[j]
                else:
                    j += 1
        # add new details
        v = tlist1[i]
        if is_implication(v) or is_equality(v):
            v, univs = unquantify(screen, v, False)
            c1 = get_constants(screen, tl, v.left)
            c2 = get_constants(screen, tl, v.right)
            nc1 = get_constants(screen, tl, complement_tree(v.left))
            nc2 = get_constants(screen, tl, complement_tree(v.right))
            m1 = metavars_used(v.left)
            m2 = metavars_used(v.right)
            mv = filter(lambda x : x not in m1, m2)
            nmv = filter(lambda x : x not in m2, m1)
            dat = AutoData(i, c1, c2, nc1, nc2)
            compute_score(screen, tl, dat, True)
            dat.mv_inc = len(list(mv))
            dat.nmv_inv = len(list(nmv))
            dat.defn = defn
            compute_direction(atab, dat)
            insert_sort(screen, atab.hyp_impls, dat)
        else:
            c = get_constants(screen, tl, v)
            nc = get_constants(screen, tl, complement_tree(v))
            dat = AutoData(i, c, None, nc, None)
            dat.deducts = deducts
            dat.depth = depth
            compute_score(screen, tl, dat, True)
            insert_sort(screen, atab.hyp_heads, dat)
    for j in dirty2:
        deducts = 0
        if j < atab.ntars: # delete old target
            k = 0
            while k < len(atab.tar_heads):
                t = atab.tar_heads[k]
                if t.line == j:
                    deducts = atab.tar_heads[k].deducts
                    del atab.tar_heads[k]
                else:
                    k += 1
        # add new details
        v = tlist2[j]
        c = get_constants(screen, tl, v)
        nc = get_constants(screen, tl, complement_tree(v))
        dat = AutoData(j, c, None, nc, None)
        dat.deducts = deducts
        compute_score(screen, tl, dat, False)
        insert_sort(screen, atab.tar_heads, dat)

    atab.nhyps = len(tlist1)
    atab.ntars = len(tlist2)
    update_screen(screen, tl, interface, dirty1, dirty2)

def autotab_remove_deadnodes(screen, tl, atab, heads, impls, interface):
    list1 = tl.tlist1.data
    list2 = tl.tlist2.data
    dirty1 = []
    dirty2 = []
    j = 0
    while j < len(atab.hyp_heads):
        if isinstance(list1[atab.hyp_heads[j].line], DeadNode):
            dirty1.append(atab.hyp_heads[j].line)
            del atab.hyp_heads[j]
        else:
            j += 1
    j = 0
    while j < len(atab.hyp_impls):
        if isinstance(list1[atab.hyp_impls[j].line], DeadNode):
            dirty1.append(atab.hyp_impls[j].line)
            del atab.hyp_impls[j]
        else:
            j += 1
    j = 0
    while j < len(atab.tar_heads):
        if isinstance(list2[atab.tar_heads[j].line], DeadNode):
            dirty2.append(atab.tar_heads[j].line)
            del atab.tar_heads[j]
        else:
            j += 1
    if heads:
        j = 0
        while j < len(heads):
            if isinstance(list1[heads[j].line], DeadNode):
                del heads[j]
            else:
                j += 1
    if impls:
        j = 0
        while j < len(impls):
            if isinstance(list1[impls[j].line], DeadNode):
                del impls[j]
            else:
                j += 1

    return update_screen(screen, tl, interface, sorted(dirty1), sorted(dirty2))

def is_definition(screen, constants, undefined, consts, nconsts):
    """
    Determine whether the theorems listed in consts define new symbols and if
    so append them to the constants list. If the symbols are used for the first
    time but undefined put them in the undefined list. Return True if the
    given theorems form a definition.
    """
    t_heads = consts[1]
    thmlist = consts[2]
    nthmlist = nconsts[2]
    # check if the t_head defines a new symbol
    is_defn = False
    for c in t_heads:
        if c not in constants and c not in undefined:
            is_defined = True
            for thm in thmlist:
                if isinstance(thm, AutoEqNode) or isinstance(thm, AutoIffNode) or \
                   isinstance(thm, AutoImplNode):
                    if c in thm.left or c in thm.right:
                        is_defined = False
                else:
                    if c in thm:
                        is_defined = False
            if is_defined:
                constants.append(c)
                is_defn = True
            else:
                undefined.append(c)
    for thm in thmlist:
        if isinstance(thm, AutoEqNode) or isinstance(thm, AutoIffNode) or \
            isinstance(thm, AutoImplNode):
                for c in thm.left:
                    if c not in constants and c not in undefined and \
                                 c not in thm.right:
                        constants.append(c)
                        is_defn = True
                    elif c not in constants and c not in undefined:
                        undefined.append(c)
                for c in thm.right:
                    if c not in constants and c not in undefined:
                        undefined.append(c)
        else:
            for c in thm:
                if c not in constants and c not in undefined:
                    is_defn = True
                    constants.append(c)

    for thm in nthmlist:
        if isinstance(thm, AutoEqNode) or isinstance(thm, AutoIffNode) or \
            isinstance(thm, AutoImplNode):
                for c in thm.left:
                    if c not in constants and c not in undefined and \
                                 c not in thm.right:
                        constants.append(c)
                        is_defn = True
                    elif c not in constants and c not in undefined:
                        undefined.append(c)
                for c in thm.right:
                    if c not in constants and c not in undefined:
                        undefined.append(c)
        else:
            for c in thm:
                if c not in constants and c not in undefined:
                    is_defn = True
                    constants.append(c)

    return is_defn
  
def create_index(screen, tl, atab, library):
    """
    Read the library in and create an index of all theorems and definitions up
    to but not including the theorem we are trying to prove.
    """
    constants = [] # an ordered list of constants in the order they appear
    undefined = [] # list of undefined symbols
    index = []
    title = library.readline()
    while title: # check for EOF
        title = title[7:-1]
        const_str = library.readline()[0:-1]
        success, consts = parse_consts(screen, const_str)
        nconst_str = library.readline()[0:-1]
        success, nconsts = parse_consts(screen, nconst_str)
        tags = library.readline()[6:-1]
        tag_list = tags.split(' ')
        filepos = library.tell()
        if filepos == tl.loaded_theorem:
            break
        # check type constants belong to this problem
        if '#sets' in tag_list:
            defn = is_definition(screen, constants, undefined, consts, nconsts)
            index.append((title, consts, nconsts, filepos, defn))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    return index, constants, undefined

def get_autonode(screen, alist, line):
    for node in alist:
        if node.line == line:
            return node

    return None

def filter_theorems1(screen, index, type_consts, consts, extra=False):
    """
    Given a library index, filter out theorems all of whose precedents
    contain only constants in the given list and whose type constants
    are all contained in the given list.
    """
    thms = []
    for (title, c, nc, filepos, defn) in index:
        thmlist = c[2]
        nthmlist = nc[2]
        tconst = c[0]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            nthm = nthmlist[i]
            if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode) or isinstance(thm, AutoEqNode):
                tc = thm.left
                tcr = thm.right
                tnc = nthm.right
                tncl = nthm.left
                if set(tconst).issubset(type_consts):
                    if set(tc).issubset(consts):
                        if set(tcr).issubset(tc) or not set(tc).issubset(tcr):
                            thms.append((title, c, nc, filepos, i, defn))
                    if set(tnc).issubset(consts):
                        if set(tncl).issubset(tnc) or not set(tnc).issubset(tncl):
                            thms.append((title, c, nc, filepos, i, defn))
    return thms

def filter_theorems2(screen, index, consts):
    """
    Given a library index, filter out theorems all of whose consequents
    contain only constants in the given list.
    """
    thms = []
    for (title, c, nc, filepos, defn) in index:
        thmlist = c[2]
        nthmlist = nc[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            nthm = nthmlist[i]
            if isinstance(thm, AutoIffNode) or isinstance(thm, AutoEqNode):
                tc = thm.right
                tcl = thm.left
                tnc = nthm.left
                tncr = nthm.right
                if set(tc).issubset(consts):
                    if set(tcl).issubset(tc) or not set(tc).issubset(tcl):
                        thms.append((title, c, nc, filepos, i, defn))
                if set(tnc).issubset(consts):
                    if set(tncr).issubset(tnc) or not set(tnc).issubset(tncr):
                        thms.append((title, c, nc, filepos, i, defn))
    return thms

def filter_theorems3(screen, index, consts1, consts2):
    """
    Given a library index, filter out theorems which are heads that
    contain only constants in the given list.
    """
    thms = []
    for (title, c, nc, filepos, defn) in index:
        thmlist = c[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            if not isinstance(thm, AutoImplNode) and not isinstance(thm, AutoEqNode) and \
               not isinstance(thm, AutoIffNode):
                if set(thm).issubset(consts1) or set(thm).issubset(consts2):
                    thms.append((title, c, nc, filepos, i))
    return thms

def autocleanup(screen, tl, ttree):
    dirty1, dirty2 = logic.cleanup(screen, tl, ttree)
    logic.fill_macros(screen, tl)
    ok, error = update_constraints(screen, tl)
    if ok:
        ok, error = process_sorts(screen, tl)
        if not ok:
            screen.dialog(error)
    else:
        screen.dialog(error)
    return dirty1, dirty2

def update_screen(screen, tl, interface, d1, d2):
    global automation_limit
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    if d1 == None:
        dirty1 = [i for i in range(len(tlist1))]
        dirty2 = [i for i in range(len(tlist2))]
    else:
        dirty1 = d1
        dirty2 = d2
        if not d1 and not d2:
            return False # nothing to update
    if interface == 'curses':
        pad1 = screen.pad1.pad
        pad2 = screen.pad2.pad
        if d1 != None:
            screen.pad0.pad[0] = str(tl.tlist0.data[0])
            line = screen.pad0.scroll_line + screen.pad0.cursor_line
            string = screen.pad0.pad[line]
            while True:
                i = screen.pad0.scroll_char + nchars_to_chars(string, \
                        screen.pad0.scroll_char, screen.pad0.cursor_char) # current pos. within string
                if i < len(string):
                    iswide = iswide_char(string[i])
                    screen.pad0.move_right(iswide)
                else:
                    break
        for i in dirty1:
            pad1[i] = str(tlist1[i])
        for i in dirty2:
            pad2[i] = str(tlist2[i])
        while tl.tlist1.line != tl.tlist1.len():
            screen.pad1.cursor_down()
            screen.pad1.refresh()
            tl.tlist1.line += 1
        tl.tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
        tl.tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
        screen.pad0.refresh()
        screen.pad1.refresh()
        screen.pad2.refresh()
        screen.focus.refresh()
    elif interface == 'javascript':
        dirtytxt0 = '' # don't display qz during automation
        dirtytxt1 = [str(tlist1[i]) for i in dirty1]
        dirtytxt2 = [str(tlist2[i]) for i in dirty2]
        emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
             'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2, 'reset_mode': False})
    return len(tl.tlist1.data) > automation_limit

def check_duplicates(screen, tl, ttree, n1, n2, tar, interface):
    """
    If n2 is equal to the number of targets in the tableau, check hypotheses
    starting at index n1 for duplicates with prior hypotheses (up to) possibly
    different metavariable indices. If any duplicates are found, they are
    replaced with DeadNode.
    If n2 is not equal to the number of targets and if targets are *all*
    duplicate from the given index, they and any hypotheses that can only
    be used to prove those targets are also replaced with DeadNode.
    The function returns True if there were *any* hypotheses or targets
    checked starting at the given indices which were not duplicate.
    """
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    dirty1 = []
    dirty2 = []
    nodup_found = False
    if n2 == len(tlist2): # only check if not checking targets
        for i in range(n1, len(tlist1)):
            nodup = True
            for j in range(n1):
                is_line = isinstance(tlist1[i], SubsetneqNode) and isinstance(tlist1[i].left, SymbolNode) and tlist1[i].left.name() == '\\emptyset'
                if is_duplicate_upto_metavars(tlist1[i], tlist1[j]):
                    if tl.tlist1.dependency(i) == tl.tlist1.dependency(j): # same dependency information
                        tlist1[i] = DeadNode(tlist1[i])
                        dirty1.append(i)
                        nodup = False
            if nodup:
                nodup_found = True
    dup2 = True
    for i in range(n2, len(tlist2)):
        dup = False
        for j in range(n2):
            if is_duplicate_upto_metavars(tlist2[i], tlist2[j]) and \
               target_depends(screen, tl, ttree, i, j):
                dup = True
        if not dup:
            dup2 = False
    if dup2:
        for i in range(n2, len(tlist2)):
            for j in range(n1, len(tlist1)):
                if deps_defunct(screen, tl, ttree, i, j):
                    tlist1[j] = DeadNode(tlist1[j])
                    dirty1.append(j)
            tlist2[i] = DeadNode(tlist2[i])
            dirty2.append(i)
    else:
        nodup_found = True
    update_screen(screen, tl, interface, dirty1, dirty2)
    return nodup_found
    
def check_trivial(screen, tl, atab, n1, interface):
    tlist1 = tl.tlist1.data
    dirty1 = []
    for i in range(n1, len(tlist1)):
        tree = tlist1[i]
        if isinstance(tree, ImpliesNode):
            if str(tree.left) == str(tree.right):
                tlist1[i] = DeadNode(tlist1[i])
                dirty1.append(i)
            elif isinstance(tree.right, EqNode):
                if str(tree.right.left) == str(tree.right.right):
                    tlist1[i] = DeadNode(tlist1[i])
                    dirty1.append(i)
        elif isinstance(tree, EqNode):
            if str(tree.left) == str(tree.right):
                tlist1[i] = DeadNode(tlist1[i])
                dirty1.append(i)
    if dirty1:
        update_screen(screen, tl, interface, dirty1, [])
        return False
    return True

def check_sizes(screen, tl, atab, n1, n2, interface):
    """
    Check for and remove hyps/tars whose type sizes exceed the maximum type
    sizes allowed (initially the maximum sizes in the initial tableau)
    """
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    dirty1 = []
    dirty2 = []
    nooversize_found = False
    if n2 == len(tlist2): # only check if not checking targets
        for i in range(n1, len(tlist1)):
            if not isinstance(tlist1[i], DeadNode):
                d, w, f = max_type_size(screen, tl, tlist1[i])
                if d > atab.max_depth or w > atab.max_width or f > atab.function_depth:
                    tlist1[i] = DeadNode(tlist1[i])
                    dirty1.append(i)
                else:
                    nooversize_found = True
    else: # reasoning back so update max function_depth
        for i in range(n1, len(tlist1)):
            if not isinstance(tlist1[i], DeadNode):
                d, w, f = max_type_size(screen, tl, tlist1[i])
                atab.max_depth = max(d, atab.max_depth)
                atab.max_width = max(w, atab.max_width)
                atab.function_depth = max(f, atab.function_depth)
        for i in range(n2, len(tlist2)):
            if not isinstance(tlist2[i], DeadNode):
                d, w, f = max_type_size(screen, tl, tlist2[i])
                atab.max_depth = max(d, atab.max_depth)
                atab.max_width = max(w, atab.max_width)
                atab.function_depth = max(f, atab.function_depth)
    for i in range(n2, len(tlist2)):
        if not isinstance(tlist2[i], DeadNode):
            d, w, f = max_type_size(screen, tl, tlist2[i])
            if d > atab.max_depth or w > atab.max_width:
                for j in range(n1, len(tlist1)):
                    if deps_defunct(screen, tl, ttree, i, j):
                        tlist1[j] = DeadNode(tlist1[j])
                        dirty1.append(j)
                tlist2[i] = DeadNode(tlist2[i])
                dirty2.append(i)
            else:
                nooversize_found = True
    update_screen(screen, tl, interface, dirty1, dirty2)
    return nooversize_found

def automate(screen, tl, ttree, interface='curses'):
    global automation_limit
    libthms_loaded = dict() # keep track of which library theorems we loaded, and where
    fake_ttree = TargetNode(-1, []) # used for fake loading of library results
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    atab = AutoTab(screen, tl) # initialise automation data structure
    library = open("library.dat", "r")
    index, constants, undefined = create_index(screen, tl, atab, library)
    atab.constants = constants
    done = False # whether all targets are proved
    current_depth = 1 # depth we are currently searching to
    depth_progress = False # whether we've made progress at current depth
    start1 = 0
    start2 = 0
    tar_heads_exhausted = [] # heads for which we've already tried everything
    count = 0
    while True: # keep going until theorem proved or progress stalls
        progress = False
        hyp_heads_exhausted = [] # heads for which we've already tried everything
        screen.debug("Getting new target")
        for tar in atab.tar_heads:
            if tar in tar_heads_exhausted:
                continue
            screen.debug("Got new target")
            hprogress = False # whether some progress is made on the hypothesis side
            tprogress = False # whether some progress is made on the target side
            # get next unproved target
            i = tar.line
            # find all target compatible hypotheses
            heads = [] # list of autonodes for target compatible hyp_heads
            impls = [] # list of autonodes for target compatible hyp_impls
            hypc = []
            tarc = tar.const1
            for v in atab.hyp_heads:
                if deps_compatible(screen, tl, ttree, i, v.line):
                    insert_sort(screen, heads, v)
                    hypc = list_merge(hypc, v.const1)
            for v in atab.hyp_impls:
                if deps_compatible(screen, tl, ttree, i, v.line):
                    insert_sort(screen, impls, v)
                    c = list_merge(v.const1, v.const2)
                    hypc = list_merge(hypc, c)
            # first see if there are any theorems/defns to load which are not implications
            libthms = filter_theorems3(screen, index, hypc, tarc)
            for (title, c, nc, filepos, line) in libthms:
                headc = c[2][line]
                # check to see if constants of libthm are among the hyp constants hypc
                if set(headc).issubset(hypc):
                    # check to see if thm already loaded, if not, load it
                    if filepos not in libthms_loaded:
                        progress = True
                        screen.debug(title)
                        logic.library_import(screen, tl, library, filepos)
                        n1 = len(tl.tlist1.data)
                        n2 = len(tl.tlist1.data)       
                        j = len(tl.tlist1.data) - 1
                        update_autotab(screen, tl, atab, [j], [], interface, 0)
                        libthms_loaded[filepos] = j
                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                        update_autotab(screen, tl, atab, dirty1, dirty2, interface, 0)
                        update_screen(screen, tl, interface, dirty1, dirty2)
                        dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree, start1, start2)
                        start1 = len(tlist1)
                        start2 = len(tlist2)
                        update_screen(screen, tl, interface, dirty1, dirty2)
                        if autotab_remove_deadnodes(screen, tl, atab, heads, impls, interface):
                            library.close()
                            automation_limit += automation_increment
                            return False
                        if done:
                            library.close()
                            return True
                        screen.debug("New non-implication thm loaded")
            if isinstance(tlist2[tar.line], DeadNode):
                break
            # try to find a theorem that applies to the target
            libthms = filter_theorems2(screen, index, tarc)
            for (title, c, nc, filepos, line, defn) in libthms:
                implc = c[2][line].left
                nimplc = nc[2][line].right
                pos = set(implc).issubset(hypc)
                neg = set(nimplc).issubset(hypc)
                # check to see if constants of libthm are among the hyp constants hypc
                if (pos or neg or \
                    not hypc or not atab.hyp_impls or not atab.hyp_heads):
                    # check to see if thm already loaded
                    line2 = tar.line
                    unifies1 = False
                    unifies2 = False
                    unifies3 = False
                    if filepos in libthms_loaded:
                        j = libthms_loaded[filepos] # get position loaded in tableau
                        tnode = get_autonode(screen, atab.hyp_impls, j + line)
                        if tnode and tar.line not in tnode.applied:
                            tnode.applied.append(tar.line)
                            thm = tlist1[j + line]
                            thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                            if isinstance(thm, ImpliesNode):
                                thm, _ = relabel(screen, tl, univs, thm, True)
                                prec, u = unquantify(screen, thm.right, False)
                                if not isinstance(prec, AndNode):
                                    # check if precedent unifies with hyp
                                    unifies1, assign, macros = unify(screen, tl, prec, tlist2[line2])
                                if not unifies1:
                                    prec, u = unquantify(screen, thm.left, True)
                                    if not isinstance(prec, AndNode):
                                        # check if precedent unifies with hyp
                                        unifies2, assign, macros = unify(screen, tl, complement_tree(prec), tlist2[line2])
                            elif isinstance(thm, EqNode):
                                unifies3, _, _ = logic.limited_equality_substitution(screen, tl, ttree, None, \
                                                                            j + line, line2, False, True)
                    else: # library theorem not yet loaded
                        fake_tl = TreeList()
                        fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
                        fake_tl.stree = tl.stree # copy sort tree from tl
                        sorts_mark(screen, tl)
                        logic.library_import(screen, fake_tl, library, filepos)
                        autocleanup(screen, fake_tl, fake_ttree)
                        thm = fake_tl.tlist1.data[line]
                        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                        thm, _ = relabel(screen, fake_tl, univs, thm, True)
                        if isinstance(thm, ImpliesNode):
                            prec, u = unquantify(screen, thm.right, False)
                            # check theorem has only one precedent
                            if not isinstance(prec, AndNode):
                                # check if precedent unifies with hyp
                                unifies1, assign, macros = unify(screen, fake_tl, prec, tlist2[line2])
                            if not unifies1:
                                prec, u = unquantify(screen, thm.left, True)
                                unifies2, assign, macros = unify(screen, fake_tl, complement_tree(prec), tlist2[line2])
                        elif isinstance(thm, EqNode):
                            fake_tl.tlist2.data.append(tlist2[line2])
                            if isinstance(tlist2[line2], DeadNode):
                                screen.dialog(str(line2))
                            unifies3, _, _ = logic.limited_equality_substitution(screen, fake_tl, ttree, None, \
                                                                            line, len(fake_tl.tlist2.data) - 1, False, True)
                            del fake_tl.tlist2.data[len(fake_tl.tlist2.data) - 1]
                        if unifies1 or unifies2 or unifies3:
                            # transfer library result to tableau
                            dirty1 = []
                            dirty2 = []
                            j = len(tlist1)
                            fake_tlist0 = fake_tl.tlist0.data
                            if fake_tlist0:
                                append_quantifiers(tl.tlist0.data, fake_tlist0[0])
                            fake_list1 = fake_tl.tlist1.data
                            for k in range(len(fake_list1)):
                                append_tree(tlist1, fake_list1[k], dirty1)
                            libthms_loaded[filepos] = j
                            tl.vars = fake_tl.vars
                            tl.stree = fake_tl.stree
                            update_autotab(screen, tl, atab, dirty1, dirty2, interface, 0, defn)
                            tnode = get_autonode(screen, atab.hyp_impls, j + line)
                            tnode.applied.append(tar.line)
                        else:
                            sorts_rollback(screen, tl)
                    if unifies1 or unifies2 or unifies3:
                        line1 = j + line
                        # apply modus ponens
                        dep = tl.tlist1.dependency(line1)
                        dep = target_compatible(screen, tl, ttree, dep, line2, False)
                        if dep:
                            n1 = len(tl.tlist1.data)
                            n2 = len(tl.tlist2.data)
                            var1 = metavars_used(tlist1[line1].left)
                            var2 = metavars_used(tlist1[line1].right)
                            if (defn and ((unifies1 and not set(tnode.const2).issubset(tnode.const1)) or \
                                            (unifies2 and not set(tnode.const1).issubset(tnode.const2)))) or \
                                                (unifies1 and set(var1).issubset(var2)) or \
                                                (unifies2 and set(var2).issubset(var1))  or unifies3:
                                if unifies1:
                                    success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], False)
                                elif unifies2:
                                    success, dirty1, dirty2 = logic.modus_tollens(screen, tl, ttree, dep, line1, [line2], False)
                                elif unifies3:
                                    success, dirty1, dirty2 = logic.limited_equality_substitution(screen, tl, ttree, dep, line1, line2, False, False)
                                if success:
                                    tar.deducts += 1
                                    adjust_score(screen, tl, atab, tar.line, False)
                                    update_autotab(screen, tl, atab, dirty1, dirty2, interface, 0, defn)
                                    dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                    update_autotab(screen, tl, atab, dirty1, dirty2, interface, 0, defn)
                                    update_screen(screen, tl, interface, dirty1, dirty2)
                                    c1 = check_duplicates(screen, tl, ttree, n1, n2, i, interface)
                                    c2 = check_sizes(screen, tl, atab, n1, n2, interface)
                                    if c1 and c2:
                                        tprogress = True
                                        progress = True
                                        dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree, start1, start2)
                                        start1 = len(tlist1)
                                        start2 = len(tlist2)
                                        update_screen(screen, tl, interface, dirty1, dirty2)
                                        if done:
                                            library.close()
                                            return True
                                        tar_heads_exhausted = []
                                        screen.debug("New target created")
                                    if autotab_remove_deadnodes(screen, tl, atab, heads, impls, interface):
                                        library.close()
                                        automation_limit += automation_increment
                                        return False
                                    if c1 and c2:
                                        break
            if tprogress:
                break
            # find all consequences of individual hypotheses (Fredy's ball)
            for hyp in heads:
                if hyp in hyp_heads_exhausted:
                    continue
                progress = False
                line2 = hyp.line
                hc = hyp.const1
                ht = get_constants_qz(screen, tl, tl.tlist0.data[0]) if tl.tlist0.data else []
                # first check if any hyp_impls can be applied to head
                for imp in impls:
                    if imp.line in hyp.applied:
                        continue
                    hyp.applied.append(imp.line)
                    line1 = imp.line
                    pos = set(imp.const1).issubset(hc) and imp.mv_inc == 0 and imp.ltor
                    neg = set(imp.nconst2).issubset(hc) and imp.nmv_inc == 0 and imp.rtol
                    if pos or neg:
                        unifies1 = False
                        unifies2 = False
                        unifies3 = False
                        v1 = vars_used(screen, tl, tlist1[line1])
                        v2 = vars_used(screen, tl, tlist1[line2])
                        if v1 or v2: # ensure not applying metavar thm to metavar head
                            thm = tlist1[line1]
                            thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                            if isinstance(thm, ImpliesNode):
                                if pos:
                                    prec, u = unquantify(screen, thm.left, True)
                                    if not isinstance(prec, AndNode):
                                        # check if precedent unifies with hyp
                                        unifies1, assign, macros = unify(screen, tl, prec, tlist1[line2])
                                        # check all metavars were assigned
                                        #if unifies1 and metavars_used(substitute(deepcopy(prec), assign)):
                                        #    unifies1 = False
                                if neg:
                                    prec, u = unquantify(screen, thm.right, True)
                                    if not isinstance(prec, AndNode):
                                        # check if neg consequent unifies with hyp
                                        comp = complement_tree(prec)
                                        unifies2, assign, macros = unify(screen, tl, comp, tlist1[line2])
                                        # check all metavars were assigned
                                        #if unifies2 and metavars_used(substitute(deepcopy(comp), assign)):
                                        #    unifies2 = False
                            elif isinstance(thm, EqNode):
                                unifies3, _, _ = logic.limited_equality_substitution(screen, tl, ttree, None, \
                                                                            line1, line2, True, True)
                        if unifies1 or unifies2 or unifies3:
                            # apply modus ponens and or modus tollens
                            dep = tl.tlist1.dependency(line1)
                            dep = target_compatible(screen, tl, ttree, dep, line2, True)
                            if dep:
                                success = False
                                n1 = len(tl.tlist1.data)
                                if unifies1:
                                    success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], True)
                                if not success and unifies2:
                                    success, dirty1, dirty2 = logic.modus_tollens(screen, tl, ttree, dep, line1, [line2], True)
                                if unifies3:
                                    success, dirty1, dirty2 = logic.limited_equality_substitution(screen, tl, ttree, dep, line1, line2, True, False)
                                if success:
                                    hyp.deducts += 1
                                    adjust_score(screen, tl, atab, hyp.line, True)
                                    imp.deducts += 1
                                    adjust_score(screen, tl, atab, imp.line, True)
                                    update_autotab(screen, tl, atab, dirty1, dirty2, interface, hyp.depth+1)
                                    dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                    update_autotab(screen, tl, atab, dirty1, dirty2, interface, hyp.depth+1)
                                    update_screen(screen, tl, interface, dirty1, dirty2)
                                    c1 = check_duplicates(screen, tl, ttree, n1, len(tlist2), i, interface)
                                    c2 = check_sizes(screen, tl, atab, n1, len(tlist2), interface)
                                    c3 = check_trivial(screen, tl, atab, n1, interface)
                                    if c1 and c2 and c3:
                                        hprogress = True
                                        progress = True
                                        dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree, start1, start2)
                                        start1 = len(tlist1)
                                        start2 = len(tlist2)
                                        update_screen(screen, tl, interface, dirty1, dirty2)
                                        if done:
                                            library.close()
                                            return True
                                        hyp_heads_exhausted = []
                                        tar_heads_exhausted = []
                                        screen.debug("New hypothesis deduced")
                                    if autotab_remove_deadnodes(screen, tl, atab, heads, impls, interface):
                                        library.close()
                                        automation_limit += automation_increment
                                        return False
                                    if c1 and c2 and c3:
                                        break
                if hprogress:
                    break
                # if no progress, look for library result that can be applied to head
                libthms = filter_theorems1(screen, index, ht, hc, hyp.line == 2)
                for (title, c, nc, filepos, line, defn) in libthms:
                    if filepos < hyp.filepos_done or (filepos == hyp.filepos_done and line < hyp.line_done):
                        continue
                    hyp.filepos_done = filepos
                    hyp.line_done = line + 1
                    # check to see if thm already loaded
                    unifies1 = False
                    unifies2 = False
                    unifies3 = False
                    if filepos not in libthms_loaded: # theorem not already loaded
                        fake_tl = TreeList()
                        fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
                        fake_tl.stree = tl.stree # copy sort tree from tl
                        sorts_mark(screen, tl)
                        logic.library_import(screen, fake_tl, library, filepos)
                        autocleanup(screen, fake_tl, fake_ttree)
                        thm = fake_tl.tlist1.data[line]
                        # check theorem has only one precedent
                        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                        if isinstance(thm, ImpliesNode):
                            m1 = metavars_used(thm.left)
                            m2 = metavars_used(thm.right)
                            mv = filter(lambda x : x not in m1, m2)
                            nmv = filter(lambda x : x not in m2, m1)
                            mv_inc = len(list(mv))
                            nmv_inc = len(list(nmv))
                            prec, u = unquantify(screen, thm.left, True)
                            if not isinstance(prec, AndNode) and mv_inc == 0:
                                # check if precedent unifies with hyp
                                v1 = vars_used(screen, tl, prec)
                                v2 = vars_used(screen, tl, tlist1[line2])
                                if v1 or v2: # ensure not applying metavar thm to metavar head
                                    unifies1, assign, macros = unify(screen, fake_tl, prec, tlist1[line2])
                            if not unifies1:
                                prec, u = unquantify(screen, thm.right, False)
                                if not isinstance(prec, AndNode) and nmv_inc == 0:
                                    # check if precedent unifies with hyp
                                    v1 = vars_used(screen, tl, prec)
                                    v2 = vars_used(screen, tl, tlist1[line2])
                                    if v1 or v2: # ensure not applying metavar thm to metavar head
                                        unifies2, assign, macros = unify(screen, fake_tl, complement_tree(prec), tlist1[line2])
                        elif isinstance(thm, EqNode):
                            fake_tl.tlist1.data.append(tlist1[line2])
                            unifies3, _, _ = logic.limited_equality_substitution(screen, fake_tl, ttree, None, \
                                                                            line, len(fake_tl.tlist1.data) - 1, True, True)
                            del fake_tl.tlist1.data[len(fake_tl.tlist1.data) - 1]
                        if unifies1 or unifies2 or unifies3:
                            # transfer library result to tableau
                            hprogress = True
                            progress = True
                            dirty1 = []
                            dirty2 = []
                            j = len(tlist1)
                            fake_tlist0 = fake_tl.tlist0.data
                            if fake_tlist0:
                                append_quantifiers(tl.tlist0.data, fake_tlist0[0])
                            fake_list1 = fake_tl.tlist1.data
                            for k in range(len(fake_list1)):
                                append_tree(tlist1, fake_list1[k], dirty1)
                            libthms_loaded[filepos] = j
                            tl.vars = fake_tl.vars
                            tl.stree = fake_tl.stree
                            update_autotab(screen, tl, atab, dirty1, dirty2, interface, hyp.depth+1, defn)
                            screen.debug("New library result loaded")
                            break
                        else:
                            sorts_rollback(screen, tl)
                if hprogress:
                    break
                hyp_heads_exhausted.append(hyp)
            if hprogress:
                break
        if not progress:
            dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree, start1, start2)
            start1 = len(tlist1)
            start2 = len(tlist2)
            update_screen(screen, tl, interface, dirty1, dirty2)
            if autotab_remove_deadnodes(screen, tl, atab, None, None, interface):
                library.close()
                automation_limit += automation_increment
                return False
            if done:
                library.close()
                return True
            screen.debug("Final fail")
            return False


        