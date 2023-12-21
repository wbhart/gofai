from utility import is_implication, get_constants, get_init_vars, list_merge, deps_compatible, \
     TargetNode, update_constraints, process_sorts, append_tree, unquantify, target_compatible, \
     append_quantifiers, relabel, deps_defunct, is_duplicate_upto_metavars, metavars_used, \
     vars_used, max_type_size, complement_tree
from autoparse import parse_consts
from moves import check_targets_proved
from unification import unify
from nodes import DeadNode, AutoImplNode, AutoEqNode, AutoIffNode, ImpliesNode, AndNode, \
     SymbolNode, NeqNode, ForallNode
from tree import TreeList
from interface import nchars_to_chars, iswide_char
from copy import deepcopy
import logic

automation_limit = 150 # number of lines in hypothesis pane before automation gives up

try:
    from flask import Flask, render_template
    from flask_socketio import SocketIO, emit
except:
    pass

class AutoData:
    def __init__(self, line, version, const1, const2, nconst1, nconst2):
        self.line = line # line in the hypothesis or target pane
        self.version = version # how many times has this line been changed
        self.const1 = const1 # constants on left side of implication or constants in predicate
        self.const2 = const2 # constants on right side of implication
        self.nconst1 = nconst1 # negated constants on left side of implication or constants in predicate
        self.nconst2 = nconst2 # negated constants on right side of implication
        self.applied = [] # list of heads that have been applied to this
        self.num_mv = 0 # number of metavariables impl will increase or head has been increased

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
        qz_data = [AutoData(0, 0, get_constants(screen, tl, tlist0[0]), None, None, None)] if tlist0 else []
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
                dat = AutoData(i, 0, c1, c2, nc1, nc2)
                hyp_impls.append(dat)
                dat.num_mv = len(metavars_used(v.right)) - len(metavars_used(v.left))
            else:
                c = get_constants(screen, tl, v)
                nc = get_constants(screen, tl, complement_tree(v))
                hyp_heads.append(AutoData(i, 0, c, None, nc, None))
        for j in range(len(tlist2)):
           v = tlist2[j]
           d, w, f = max_type_size(screen, tl, v)
           max_depth = max(max_depth, d)
           max_width = max(max_width, w)
           function_depth = max(function_depth, f)
           c = get_constants(screen, tl, v)
           nc = get_constants(screen, tl, complement_tree(v))
           tar_heads.append(AutoData(j, 0, c, None, nc, None))
        self.hyp_heads = hyp_heads
        self.hyp_impls = hyp_impls
        self.tar_heads = tar_heads
        self.thms = []
        self.max_depth = max_depth
        self.max_width = max_width
        self.function_depth = function_depth

def update_autotab(screen, tl, atab, dirty1, dirty2, interface, mv_diff=0):
    """
    Given an AutoTab data structure and a list of modified/added hypotheses
    (dirty1) and a list of modified/added targets (dirty2), update the data
    in the AutoTab structure to reflect current reality.
    """
    tlist0 = tl.tlist0.data
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    for i in dirty1:
        version = -1
        if i < atab.nhyps: # delete old hypothesis
            j = 0
            while j < len(atab.hyp_heads):
                t = atab.hyp_heads[j]
                if t.line == i:
                    version = atab.hyp_heads[j].version
                    del atab.hyp_heads[j]
                else:
                    j += 1
            j = 0
            while j < len(atab.hyp_impls):
                t = atab.hyp_impls[j]
                if t.line == i:
                    version = atab.hyp_impls[j].version
                    del atab.hyp_impls[j]
                else:
                    j += 1
        # add new details
        v = tlist1[i]
        if is_implication(v):
            v, univs = unquantify(screen, v, False)
            c1 = get_constants(screen, tl, v.left)
            c2 = get_constants(screen, tl, v.right)
            nc1 = get_constants(screen, tl, complement_tree(v.left))
            nc2 = get_constants(screen, tl, complement_tree(v.right))
            dat = AutoData(i, version + 1, c1, c2, nc1, nc2)
            atab.hyp_impls.append(dat)
            dat.num_mv = len(metavars_used(v.right)) - len(metavars_used(v.left))
        else:
            c = get_constants(screen, tl, v)
            nc = get_constants(screen, tl, complement_tree(v))
            dat = AutoData(i, version + 1, c, None, nc, None)
            atab.hyp_heads.append(dat)
            dat.num_mv = mv_diff
    for j in dirty2:
        version = -1
        if j < atab.ntars: # delete old target
            k = 0
            while k < len(atab.tar_heads):
                t = atab.tar_heads[k]
                if t.line == j:
                    version = atab.tar_heads[k].version
                    del atab.tar_heads[k]
                else:
                    k += 1
        # add new details
        v = tlist2[j]
        c = get_constants(screen, tl, v)
        nc = get_constants(screen, tl, complement_tree(v))
        atab.tar_heads.append(AutoData(j, version + 1, c, None, nc, None))
            
    atab.nhyps = len(tlist1)
    atab.ntars = len(tlist2)
    update_screen(screen, tl, interface, dirty1, dirty2)

def autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
    list1 = tl.tlist1.data
    list2 = tl.tlist1.data
    dirty1 = []
    dirty2 = []
    for i in range(n1, len(list1)):
        if isinstance(list1[i], DeadNode):
            found = False
            j = 0
            while j < len(atab.hyp_heads):
                if atab.hyp_heads[j].line == i:
                    dirty1.append(i)
                    del atab.hyp_heads[j]
                    found = True
                    break
                else:
                    j += 1
            if not found:
                j = 0
                while j < len(atab.hyp_impls):
                    if atab.hyp_impls[j].line == i:
                        dirty1.append(i)
                        del atab.hyp_impls[j]
                        break
                    else:
                        j += 1
    for i in range(n2, len(list2)):
        if isinstance(list2[i], DeadNode):
            j = 0
            while j < len(atab.tar_heads):
                if atab.tar_heads[j].line == i:
                    dirty2.append(i)
                    del atab.tar_heads[j]
                    break
                else:
                    j += 1
    return update_screen(screen, tl, interface, dirty1, dirty2)

def create_index(screen, tl):
    """
    Read the library in and create an index of all theorems and definitions up
    to but not including the theorem we are trying to prove.
    """
    library = open("library.dat", "r")
    index = []
    title = library.readline()
    while title: # check for EOF
        title = title[7:-1]
        const_str = library.readline()[0:-1]
        success, consts = parse_consts(screen, const_str)
        nconst_str = library.readline()[0:-1]
        success, nconsts = parse_consts(screen, nconst_str)
        #term_str = library.readline()[0:-1]
        tags = library.readline() # skip tags
        filepos = library.tell()
        if filepos == tl.loaded_theorem:
            break
        index.append((title, consts, nconsts, filepos))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    return index

def get_autonode(screen, alist, line):
    """
    Given a list of AutoData structs, find the one with the given line if it
    exists and return it. Otherwise, return None.
    """
    for k in range(len(alist)):
        if alist[k].line == line:
            return alist[k]
    return None

def filter_theorems1(screen, index, type_consts, consts):
    """
    Given a library index, filter out theorems all of whose precedents
    contain only constants in the given list and whose type constants
    are all contained in the given list.
    """
    thms = []
    for (title, c, nc, filepos) in index:
        thmlist = c[2]
        nthmlist = nc[2]
        tconst = c[0]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            nthm = nthmlist[i]
            if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode):
                tc = thm.left
                tnc = nthm.right
                if set(tconst).issubset(type_consts):
                    if set(tc).issubset(consts):
                        thms.append((title, c, nc, filepos, i))
                    elif set(tnc).issubset(consts):
                        thms.append((title, c, nc, filepos, i))
    return thms

def filter_theorems2(screen, index, consts, mode):
    """
    Given a library index, filter out theorems all of whose consequents
    contain only constants in the given list.
    """
    thms = []
    for (title, c, nc, filepos) in index:
        thmlist = c[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            if (mode == 0 and isinstance(thm, AutoImplNode)) or isinstance(thm, AutoIffNode):
                tc = thm.right
                if set(tc).issubset(consts):
                    thms.append((title, c, nc, filepos, i))
    return thms

def filter_theorems3(screen, index, consts1, consts2):
    """
    Given a library index, filter out theorems which are heads that
    contain only constants in the given list.
    """
    thms = []
    for (title, c, nc, filepos) in index:
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

def check_duplicates(screen, tl, ttree, n1, n2, interface):
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
                if is_duplicate_upto_metavars(tlist1[i], tlist1[j]):
                    tlist1[i] = DeadNode(tlist1[i])
                    dirty1.append(i)
                    nodup = False
            if nodup:
                nodup_found = True
    dup2 = True
    for i in range(n2, len(tlist2)):
        dup = False
        for j in range(n2):
            if is_duplicate_upto_metavars(tlist2[i], tlist2[j]):
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
    libthms_loaded = dict() # keep track of which library theorems we loaded, and where
    fake_ttree = TargetNode(-1, []) # used for fake loading of library results
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    atab = AutoTab(screen, tl) # initialise automation data structure
    index = create_index(screen, tl)
    done = False # whether all targets are proved
    mode = 0 # mode 0 = no adding tar metavars, mode 1 = add tar metavars with iffs
    while True: # keep going until theorem proved or progress stalls
        # get next unproved target
        i = 0
        made_progress = False
        while i < len(tlist2):
            while i < len(tlist2):
                if not isinstance(tlist2[i], DeadNode):
                    break
                i += 1
            if i >= len(tlist2):
                break
            # find all target compatible hypotheses
            hyps = []
            for j in range(len(tlist1)):
                if deps_compatible(screen, tl, ttree, i, j):
                    hyps.append(j)
            # find all consequences of individual hypotheses (Fredy's ball)
            hprogress = False # whether some progress is made on the hypothesis side
            for j in hyps:
                hyp = get_autonode(screen, atab.hyp_heads, j)
                if hyp: # hypothesis is a head
                    progress = False
                    line2 = hyp.line
                    hc = hyp.const1
                    ht = get_constants(screen, tl, tl.tlist0.data[0]) if tl.tlist0.data else []
                    # first check if any hyp_impls can be applied to head
                    for imp in atab.hyp_impls:
                        pos = set(imp.const1).issubset(hc)
                        neg = set(imp.nconst2).issubset(hc)
                        if imp.num_mv <= 0 and (pos or neg):
                            unifies1 = False
                            unifies2 = False
                            line1 = imp.line
                            if (hyp.line, hyp.version, True) not in imp.applied:
                                v1 = vars_used(screen, tl, tlist1[line1])
                                v2 = vars_used(screen, tl, tlist1[line2])
                                if v1 or v2: # ensure not applying metavar thm to metavar head
                                    imp.applied.append((hyp.line, hyp.version, True))
                                    thm = tlist1[line1]
                                    thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                    if isinstance(thm, ImpliesNode):
                                        if pos:
                                            prec, u = unquantify(screen, thm.left, True)
                                            if not isinstance(prec, AndNode):
                                                # check if precedent unifies with hyp
                                                unifies1, assign, macros = unify(screen, tl, prec, tlist1[line2])
                                        if neg:
                                            prec, u = unquantify(screen, thm.right, True)
                                            if not isinstance(prec, AndNode):
                                                # check if neg consequent unifies with hyp
                                                unifies2, assign, macros = unify(screen, tl, complement_tree(prec), tlist1[line2])
                            if unifies1 or unifies2:
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
                                    if success:
                                        mv_diff = hyp.num_mv + max(imp.num_mv, 0)
                                        update_autotab(screen, tl, atab, dirty1, dirty2, interface, mv_diff)
                                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                        update_autotab(screen, tl, atab, dirty1, dirty2, interface, mv_diff)
                                        dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree)
                                        update_screen(screen, tl, interface, dirty1, dirty2)
                                        c1 = check_duplicates(screen, tl, ttree, n1, len(tlist2), interface)
                                        c2 = check_sizes(screen, tl, atab, n1, len(tlist2), interface)
                                        if c1 and c2:
                                            hprogress = True
                                            progress = True
                                        if autotab_remove_deadnodes(screen, tl, atab, n1, len(tlist2), interface):
                                            return False
                                        if done:
                                            update_screen(screen, tl, interface, None, None)
                                            return True
                    # if no progress, look for library result that can be applied to head
                    if not progress:
                        libthms = filter_theorems1(screen, index, ht, hc)
                        for (title, c, nc, filepos, line) in libthms:
                            # check to see if thm already loaded
                            unifies1 = False
                            unifies2 = False
                            if filepos in libthms_loaded:
                                j = libthms_loaded[filepos] # get position loaded in tableau
                                tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                if tnode and tnode.num_mv <= 0 and \
                                   (hyp.line, hyp.version, True) not in tnode.applied:
                                    tnode.applied.append((hyp.line, hyp.version, True))
                                    thm = tlist1[j + line]
                                    thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                    if isinstance(thm, ImpliesNode):
                                        prec, u = unquantify(screen, thm.left, True)
                                        if not isinstance(prec, AndNode):
                                            # check if precedent unifies with hyp
                                            v1 = vars_used(screen, tl, prec)
                                            v2 = vars_used(screen, tl, tlist1[line2])
                                            if v1 or v2: # ensure not applying metavar thm to metavar head
                                                unifies1, assign, macros = unify(screen, tl, prec, tlist1[line2])
                                        if not unifies1:
                                            prec, u = unquantify(screen, thm.right, True)
                                            if not isinstance(prec, AndNode):
                                                # check if precedent unifies with hyp
                                                v1 = vars_used(screen, tl, prec)
                                                v2 = vars_used(screen, tl, tlist1[line2])
                                                if v1 or v2: # ensure not applying metavar thm to metavar head
                                                    unifies2, assign, macros = unify(screen, tl, complement_tree(prec), tlist1[line2])
                            else: # library theorem not yet loaded
                                fake_tl = TreeList()
                                fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
                                fake_tl.stree = deepcopy(tl.stree) # copy sort tree from tl
                                library = open("library.dat", "r")
                                logic.library_import(screen, fake_tl, library, filepos)
                                library.close()
                                autocleanup(screen, fake_tl, fake_ttree)
                                thm = fake_tl.tlist1.data[line]
                                # check theorem has only one precedent
                                thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                if isinstance(thm, ImpliesNode):
                                    mv_diff = len(metavars_used(thm.right)) - len(metavars_used(thm.left))
                                    prec, u = unquantify(screen, thm.left, True)
                                    if not isinstance(prec, AndNode) and mv_diff <= 0:
                                        # check if precedent unifies with hyp
                                        v1 = vars_used(screen, tl, prec)
                                        v2 = vars_used(screen, tl, tlist1[line2])
                                        if v1 or v2: # ensure not applying metavar thm to metavar head
                                            unifies1, assign, macros = unify(screen, fake_tl, prec, tlist1[line2])
                                    if not unifies1:
                                        prec, u = unquantify(screen, thm.right, True)
                                        if not isinstance(prec, AndNode) and mv_diff <= 0:
                                            # check if precedent unifies with hyp
                                            v1 = vars_used(screen, tl, prec)
                                            v2 = vars_used(screen, tl, tlist1[line2])
                                            if v1 or v2: # ensure not applying metavar thm to metavar head
                                                unifies2, assign, macros = unify(screen, fake_tl, complement_tree(prec), tlist1[line2])
                                    if unifies1 or unifies2:
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
                                        update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                        tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                        tnode.applied.append((hyp.line, hyp.version, True))
                            if unifies1 or unifies2:
                                line1 = j + line
                                # apply modus ponens
                                dep = tl.tlist1.dependency(line1)
                                dep = target_compatible(screen, tl, ttree, dep, line2, True)
                                if dep:
                                    n1 = len(tl.tlist1.data)
                                    success = False
                                    if unifies1:
                                        success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], True)
                                    elif unifies2:
                                        success, dirty1, dirty2 = logic.modus_tollens(screen, tl, ttree, dep, line1, [line2], True)
                                    if success:
                                        update_autotab(screen, tl, atab, dirty1, dirty2, interface, 0)
                                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                        update_autotab(screen, tl, atab, dirty1, dirty2, interface, 0)
                                        dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree)
                                        update_screen(screen, tl, interface, dirty1, dirty2)
                                        c1 = check_duplicates(screen, tl, ttree, n1, len(tlist2), interface)
                                        c2 = check_sizes(screen, tl, atab, n1, len(tlist2), interface)
                                        if c1 and c2:
                                            hprogress = True
                                        if autotab_remove_deadnodes(screen, tl, atab, n1, len(tlist2), interface):
                                            return False
                                        if done:
                                            update_screen(screen, tl, interface, None, None)
                                            return True
            tar = get_autonode(screen, atab.tar_heads, i)
            if not done and tar:
                # check if constants in target are all in hypotheses
                tarc = tar.const1
                hypc = []
                heads = [] # list of autonodes for target compatible hyp_heads
                impls = [] # list of autonodes for target compatible hyp_impls
                for k in hyps:
                    node = get_autonode(screen, atab.hyp_heads, k)
                    if node:
                        heads.append(node)
                        c = node.const1
                    else:
                        node = get_autonode(screen, atab.hyp_impls, k)
                        if node:
                            impls.append(node)
                            c = list_merge(node.const1, node.const2)
                    hypc = list_merge(hypc, c)
                tprogress = False # whether or not some progress is made on the target side
                # first see if there are any theorems/defns to load which are not implications
                libthms = filter_theorems3(screen, index, hypc, tarc)
                for (title, c, nc, filepos, line) in libthms:
                    headc = c[2][line]
                    # check to see if constants of libthm are among the hyp constants hypc
                    if set(headc).issubset(hypc):
                        # check to see if thm already loaded, if not, load it
                        if filepos not in libthms_loaded:
                            library = open("library.dat", "r")
                            logic.library_import(screen, tl, library, filepos)
                            library.close()
                            n1 = len(tl.tlist1.data)
                            n2 = len(tl.tlist1.data)       
                            j = len(tl.tlist1.data) - 1
                            update_autotab(screen, tl, atab, [j], [], interface)
                            libthms_loaded[filepos] = j
                            dirty1, dirty2 = autocleanup(screen, tl, ttree)
                            update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                            dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree)
                            update_screen(screen, tl, interface, dirty1, dirty2)
                            c1 = check_duplicates(screen, tl, ttree, n1, n2, interface)
                            c2 = check_sizes(screen, tl, atab, n1, n2, interface)
                            if c1 and c2:
                                tprogress = True
                            if autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
                                return False
                            if done:
                                update_screen(screen, tl, interface, None, None)
                                return True
                if not tprogress:
                    if not set(tarc).issubset(hypc):
                        pass # not implemented yet
                    else: # it is possible that the target can be directly proved from the hyps
                        # check if some implication among the hyps can be used
                        for imp in impls:
                            if (tar.line, tar.version, False) not in imp.applied: # not yet applied to this head
                                # check if this implication can be applied to this head
                                pass # not implemented yet
                # try to find a theorem that applies to the target
                if not tprogress: # TODO : remove the second restriction
                    libthms = filter_theorems2(screen, index, tarc, mode)
                    for (title, c, nc, filepos, line) in libthms:
                        implc = c[2][line].left
                        # check to see if constants of libthm are among the hyp constants hypc
                        if (tar.line not in tl.tars) and (set(implc).issubset(hypc) or \
                           not hypc or not atab.hyp_impls or not atab.hyp_heads):
                            # check to see if thm already loaded
                            line2 = tar.line
                            unifies = False
                            if filepos in libthms_loaded:
                                j = libthms_loaded[filepos] # get position loaded in tableau
                                tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                if tnode and (tar.line, tar.version, False) not in tnode.applied:
                                    tnode.applied.append((tar.line, tar.version, False))
                                    thm = tlist1[j + line]
                                    thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                    if isinstance(thm, ImpliesNode):
                                        thm, _ = relabel(screen, tl, univs, thm, True)
                                        prec, u = unquantify(screen, thm.right, False)
                                        if not isinstance(prec, AndNode):
                                            # check if precedent unifies with hyp
                                            unifies, assign, macros = unify(screen, tl, prec, tlist2[line2])
                            else: # library theorem not yet loaded
                                fake_tl = TreeList()
                                fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
                                fake_tl.stree = deepcopy(tl.stree) # copy sort tree from tl
                                library = open("library.dat", "r")
                                logic.library_import(screen, fake_tl, library, filepos)
                                library.close()
                                autocleanup(screen, fake_tl, fake_ttree)
                                thm = fake_tl.tlist1.data[line]
                                thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                # check theorem has only one precedent
                                if isinstance(thm, ImpliesNode):
                                    thm, _ = relabel(screen, fake_tl, univs, thm, True)
                                    prec, u = unquantify(screen, thm.right, False)
                                    if not isinstance(prec, AndNode):
                                        # check if precedent unifies with hyp
                                        unifies, assign, macros = unify(screen, fake_tl, prec, tlist2[line2])
                                        if unifies:
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
                                            update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                            tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                            tnode.applied.append((tar.line, tar.version, False))
                            if unifies:
                                line1 = j + line
                                # apply modus ponens
                                dep = tl.tlist1.dependency(line1)
                                dep = target_compatible(screen, tl, ttree, dep, line2, False)
                                if dep:
                                    n1 = len(tl.tlist1.data)
                                    n2 = len(tl.tlist2.data)
                                    var1 = metavars_used(tlist1[line1].left)
                                    var2 = metavars_used(tlist1[line1].right)
                                    if mode == 1 or set(var1).issubset(var2):
                                        success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], False)
                                        if success:
                                            update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                            dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                            update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                            dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree)
                                            update_screen(screen, tl, interface, dirty1, dirty2)
                                            c1 = check_duplicates(screen, tl, ttree, n1, n2, interface)
                                            c2 = check_sizes(screen, tl, atab, n1, n2, interface)
                                            if c1 and c2:
                                                tprogress = True
                                            if autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
                                                return False
                                            if done:
                                                update_screen(screen, tl, interface, None, None)
                                                return True
            if tprogress or not hprogress: # must move on if theorem reasoned back from
                i += 1
            if hprogress or tprogress:
                made_progress = True
        if not made_progress: # we aren't getting anywhere
            if mode < 1: # try more extreme things
                mode += 1
            else:
                update_screen(screen, tl, interface, None, None)
                return False

        