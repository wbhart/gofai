from utility import is_implication, get_constants, get_init_vars, list_merge, deps_compatible, \
     TargetNode, update_constraints, process_sorts, append_tree, unquantify, target_compatible, \
     append_quantifiers, relabel, deps_defunct, is_duplicate_upto_metavars, metavars_used, \
     vars_used, max_type_size, complement_tree, sorts_mark, sorts_rollback, is_equality, \
     target_depends, get_constants_qz
from autoparse import parse_consts
from moves import check_targets_proved
from unification import unify, substitute
from nodes import DeadNode, AutoImplNode, AutoEqNode, AutoIffNode, ImpliesNode, AndNode, \
     SymbolNode, NeqNode, ForallNode, EqNode, NotNode, FnApplNode, ElemNode, VarNode
from tree import TreeList
from interface import nchars_to_chars, iswide_char
from copy import deepcopy
import logic, math

automation_limit     = 1000 # number of lines in hypothesis pane before automation gives up
automation_increment = 300 # number of lines to add next time automation is called

try:
    from flask import Flask, render_template
    from flask_socketio import SocketIO, emit
except:
    pass

class AutoData:
    def __init__(self, line, const1, const2, nconst1, nconst2):
        self.line = line # line in the hypothesis or target pane
        self.const1 = const1 # constants on left side of implication or constants in predicate
        self.const2 = const2 # constants on right side of implication
        self.nconst1 = nconst1 # negated constants on left side of implication or constants in predicate
        self.nconst2 = nconst2 # negated constants on right side of implication
        self.applied = [] # list of heads that have been applied to this
        self.impls_done = 0 # number of largest impl checked against this head for application
        self.filepos_done = 0 # largest filepos of theorem checked against this head for application
        self.line_done = 0 # line of theorem at filepos checked against this head
        
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
        hyp_heads = []
        hyp_impls = []
        tar_heads = []
        for i in range(len(tlist1)):
            v = tlist1[i]
            if is_implication(v):
                v, univs = unquantify(screen, v, False)
                c1 = get_constants(screen, tl, v.left)
                c2 = get_constants(screen, tl, v.right)
                nc1 = get_constants(screen, tl, complement_tree(v.left))
                nc2 = get_constants(screen, tl, complement_tree(v.right))
                dat = AutoData(i, c1, c2, nc1, nc2)
                hyp_impls.append(dat)
            else:
                c = get_constants(screen, tl, v)
                nc = get_constants(screen, tl, complement_tree(v))
                ad = AutoData(i, c, None, nc, None)
                hyp_heads.append(ad)
        for j in range(len(tlist2)):
           v = tlist2[j]
           c = get_constants(screen, tl, v)
           nc = get_constants(screen, tl, complement_tree(v))
           tar_heads.append(AutoData(j, c, None, nc, None))
        self.hyp_heads = hyp_heads
        self.hyp_impls = hyp_impls
        self.tar_heads = tar_heads
        self.thms = []
        
def update_autotab(screen, tl, atab, dirty1, dirty2, interface):
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
        if i < atab.nhyps: # delete old hypothesis
            j = 0
            while j < len(atab.hyp_heads):
                t = atab.hyp_heads[j]
                if t.line == i:
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
            dat = AutoData(i, c1, c2, nc1, nc2)
            atab.hyp_impls.append(dat)
        else:
            c = get_constants(screen, tl, v)
            nc = get_constants(screen, tl, complement_tree(v))
            dat = AutoData(i, c, None, nc, None)
            atab.hyp_heads.append(dat)
    for j in dirty2:
        if j < atab.ntars: # delete old target
            k = 0
            while k < len(atab.tar_heads):
                t = atab.tar_heads[k]
                if t.line == j:
                    del atab.tar_heads[k]
                else:
                    k += 1
        # add new details
        v = tlist2[j]
        c = get_constants(screen, tl, v)
        nc = get_constants(screen, tl, complement_tree(v))
        atab.tar_heads.append(AutoData(j, c, None, nc, None))

    atab.nhyps = len(tlist1)
    atab.ntars = len(tlist2)
    update_screen(screen, tl, interface, dirty1, dirty2)

def autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
    list1 = tl.tlist1.data
    list2 = tl.tlist2.data
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

def create_index(screen, tl, library):
    """
    Read the library in and create an index of all theorems and definitions up
    to but not including the theorem we are trying to prove.
    """
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
    low = 0
    high = len(alist) - 1

    while low <= high:
        mid = (low + high) // 2
        if alist[mid].line < line:
            low = mid + 1
        elif alist[mid].line > line:
            high = mid - 1
        else:
            return alist[mid]

    return None

def filter_theorems1(screen, index):
    thms = []
    for (title, c, nc, filepos) in index:
        thmlist = c[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode) or isinstance(thm, AutoEqNode):
                thms.append((title, c, nc, filepos, i))
                
    return thms

def filter_theorems2(screen, index):
    thms = []
    for (title, c, nc, filepos) in index:
        thmlist = c[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            if (isinstance(thm, AutoImplNode)) or isinstance(thm, AutoIffNode) or isinstance(thm, AutoEqNode):
                iff = isinstance(thm, AutoIffNode)
                thms.append((title, c, nc, filepos, i, iff))
    
    return thms

def filter_theorems3(screen, index):
    thms = []
    for (title, c, nc, filepos) in index:
        thmlist = c[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            if not isinstance(thm, AutoImplNode) and not isinstance(thm, AutoEqNode) and \
               not isinstance(thm, AutoIffNode):
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
                if is_duplicate_upto_metavars(tlist1[i], tlist1[j]):
                    if deps_compatible(screen, tl, ttree, tar, j):
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

def automate(screen, tl, ttree, interface='curses'):
    global automation_limit
    libthms_loaded = dict() # keep track of which library theorems we loaded, and where
    fake_ttree = TargetNode(-1, []) # used for fake loading of library results
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    atab = AutoTab(screen, tl) # initialise automation data structure
    library = open("library.dat", "r")
    index = create_index(screen, tl, library)
    done = False # whether all targets are proved
    starting = True
    while True: # keep going until theorem proved or progress stalls
        # get next unproved target
        i = 0
        made_progress = False
        while i < len(tlist2):
            start1 = 0 if starting else len(tlist1)  # used by incremental completion checking
            start2 = 0 if starting else len(tlist2)
            starting = False
            while i < len(tlist2):
                if not isinstance(tlist2[i], DeadNode):
                    break
                i += 1
            if i >= len(tlist2):
                break
            tar = get_autonode(screen, atab.tar_heads, i)
            tprogress = False # whether or not some progress is made on the target side
            hprogress = False # whether some progress is made on the hypothesis side
                # try to find a theorem that applies to the target
            libthms = filter_theorems2(screen, index)
            for (title, c, nc, filepos, line, iff) in libthms:
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
                        update_autotab(screen, tl, atab, dirty1, dirty2, interface)
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
                        if unifies1 or unifies2 or unifies3:
                            if unifies1:
                                success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], False)
                            elif unifies2:
                                success, dirty1, dirty2 = logic.modus_tollens(screen, tl, ttree, dep, line1, [line2], False)
                            elif unifies3:
                                success, dirty1, dirty2 = logic.limited_equality_substitution(screen, tl, ttree, dep, line1, line2, False, False)
                            if success:
                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                update_screen(screen, tl, interface, dirty1, dirty2)
                                c1 = check_duplicates(screen, tl, ttree, n1, n2, i, interface)
                                if c1:
                                    tprogress = True
                                if autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False
                                break
            if tprogress:
                continue
            # find all target compatible hypotheses
            hyps = []
            for v in atab.hyp_heads:
                if deps_compatible(screen, tl, ttree, i, v.line):
                    hyps.append(v)
            # find all consequences of individual hypotheses (Fredy's ball)
            for hyp in hyps:
                line2 = hyp.line
                hc = hyp.const1
                # first check if any hyp_impls can be applied to head
                for imp in atab.hyp_impls:
                    line1 = imp.line
                    if line1 < hyp.impls_done:
                        continue
                    hyp.impls_done = line1 + 1
                    unifies1 = False
                    unifies2 = False
                    unifies3 = False
                    if True: # ensure not applying metavar thm to metavar head
                        thm = tlist1[line1]
                        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                        if isinstance(thm, ImpliesNode):
                            if True:
                                prec, u = unquantify(screen, thm.left, True)
                                if not isinstance(prec, AndNode):
                                    # check if precedent unifies with hyp
                                    unifies1, assign, macros = unify(screen, tl, prec, tlist1[line2])
                            if True:
                                prec, u = unquantify(screen, thm.right, True)
                                if not isinstance(prec, AndNode):
                                    # check if neg consequent unifies with hyp
                                    comp = complement_tree(prec)
                                    unifies2, assign, macros = unify(screen, tl, comp, tlist1[line2])
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
                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                                update_screen(screen, tl, interface, dirty1, dirty2)
                                c1 = check_duplicates(screen, tl, ttree, n1, len(tlist2), i, interface)
                                c2 = check_trivial(screen, tl, atab, n1, interface)
                                if c1 and c2:
                                    hprogress = True
                                if autotab_remove_deadnodes(screen, tl, atab, n1, len(tlist2), interface):
                                    library.close()
                                    automation_limit += automation_increment   
                                    return False
                                break
                # if no progress, look for library result that can be applied to head
                if hprogress:
                    continue
                libthms = filter_theorems1(screen, index)
                for (title, c, nc, filepos, line) in libthms:
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
                            prec, u = unquantify(screen, thm.left, True)
                            if not isinstance(prec, AndNode):
                                # check if precedent unifies with hyp
                                if True: # ensure not applying metavar thm to metavar head
                                    unifies1, assign, macros = unify(screen, fake_tl, prec, tlist1[line2])
                            if not unifies1:
                                prec, u = unquantify(screen, thm.right, False)
                                if not isinstance(prec, AndNode):
                                    # check if precedent unifies with hyp
                                    if True: # ensure not applying metavar thm to metavar head
                                        unifies2, assign, macros = unify(screen, fake_tl, complement_tree(prec), tlist1[line2])
                        elif isinstance(thm, EqNode):
                            fake_tl.tlist1.data.append(tlist1[line2])
                            unifies3, _, _ = logic.limited_equality_substitution(screen, fake_tl, ttree, None, \
                                                                            line, len(fake_tl.tlist1.data) - 1, True, True)
                            del fake_tl.tlist1.data[len(fake_tl.tlist1.data) - 1]
                        if unifies1 or unifies2 or unifies3:
                            # transfer library result to tableau
                            hprogress = True
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
                            tnode.applied.append((hyp.line, True))
                        else:
                            sorts_rollback(screen, tl)
                if hprogress:
                    break
                # see if there are any theorems/defns to load which are not implications
                libthms = filter_theorems3(screen, index)
                for (title, c, nc, filepos, line) in libthms:
                    headc = c[2][line]
                    # check to see if thm already loaded, if not, load it
                    if filepos not in libthms_loaded:
                        hprogress = True
                        logic.library_import(screen, tl, library, filepos)
                        n1 = len(tl.tlist1.data)
                        n2 = len(tl.tlist1.data)       
                        j = len(tl.tlist1.data) - 1
                        update_autotab(screen, tl, atab, [j], [], interface)
                        libthms_loaded[filepos] = j
                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                        update_autotab(screen, tl, atab, dirty1, dirty2, interface)
                        update_screen(screen, tl, interface, dirty1, dirty2)
                        if autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
                            library.close()
                            automation_limit += automation_increment
                            return False
            dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree, start1, start2)
            update_screen(screen, tl, interface, dirty1, dirty2)
            if done:
                return True
            i += 1
            if hprogress or tprogress:
                made_progress = True
        if not made_progress: # we aren't getting anywhere
            update_screen(screen, tl, interface, None, None)
            library.close()
            automation_limit += 150
            return False

        