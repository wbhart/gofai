from utility import is_implication, get_constants, get_init_vars, list_merge, deps_compatible, \
     TargetNode, update_constraints, process_sorts, append_tree, unquantify, target_compatible, \
     append_quantifiers, relabel, deps_defunct, is_duplicate_upto_metavars, metavars_used, \
     vars_used, max_type_size, complement_tree, sorts_mark, sorts_rollback, is_equality, \
     target_depends, get_constants_qz
from autoparse import parse_consts
from moves import check_targets_proved
from unification import unify, substitute
from nodes import DeadNode, AutoImplNode, AutoEqNode, AutoIffNode, ImpliesNode, AndNode, \
     SymbolNode, NeqNode, ForallNode, EqNode, NotNode, FnApplNode, SubsetneqNode, LeafNode, \
     LRNode, TupleNode
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
    def __init__(self, screen, tl, ttree, library, constants):
        tlist0 = tl.tlist0.data
        tlist1 = tl.tlist1.data
        tlist2 = tl.tlist2.data

        self.tl = tl
        self.ttree = ttree
        self.nhyps = len(tlist1)
        self.ntars = len(tlist2)
        self.vars = get_init_vars(screen, tl, tlist0[0]) if tlist0 else [] # vars in initial tableau
        self.type_consts = get_constants_qz(screen, tl, tlist0[0])
        self.constants = None
        self.libthms_loaded = dict() # keep track of which library theorems we loaded, and where
        self.library = library
        self.start1 = 0 # for incremental completion checking
        self.start2 = 0
        self.constants = constants

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

                compute_direction(self, dat)
                compute_score(screen, tl, dat, True)

                m1 = metavars_used(v.left)
                m2 = metavars_used(v.right)
                mv = filter(lambda x : x not in m1, m2)
                nmv = filter(lambda x : x not in m2, m1)

                dat.mv_inc = len(list(mv))
                dat.nmv_inv = len(list(nmv))

                hyp_impls.append(dat)
                dat.num_mv = len(metavars_used(v.right)) - len(metavars_used(v.left))
            else:
                c = get_constants(screen, tl, v)
                nc = get_constants(screen, tl, complement_tree(v))
                
                dat = AutoData(i, c, None, nc, None)

                compute_score(screen, tl, dat, True)
               
                insert_sort(screen, hyp_heads, dat)

        for j in range(len(tlist2)):
           v = tlist2[j]

           d, w, f = max_type_size(screen, tl, v)
           max_depth = max(max_depth, d)
           max_width = max(max_width, w)
           function_depth = max(function_depth, f)

           c = get_constants(screen, tl, v)
           nc = get_constants(screen, tl, complement_tree(v))

           dat = AutoData(j, c, None, nc, None)
           tar_heads.append(dat)

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

def tree_size(tree):
    if tree == None:
        return 0
    elif isinstance(tree, LeafNode):
        return 1
    elif isinstance(tree, LRNode):
        return max(tree_size(tree.left), tree_size(tree.right)) + 1
    elif isinstance(tree, TupleNode):
        return max(tree_size(arg) for arg in tree.args) + 1
    elif isinstance(tree, FnApplNode):
        if tree.args:
            return max(max(tree_size(arg) for arg in tree.args), tree_size(tree.var)) + 1
        else:
            return tree_size(tree.var) + 1
    else:
        raise Exception("Unknown type "+str(type(tree)))
    
def compute_score(screen, tl, dat, is_hyp):
    v = tl.tlist1.data[dat.line] if is_hyp else tl.tlist2.data[dat.line]
    d, w, f = max_type_size(screen, tl, v)
    dat.score = 0
    dat.score += math.log(d+1)
    dat.score += math.log(w+1)
    dat.score += math.log(f+1)
    dat.score += math.log(tree_size(v)+1)
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
    if is_impl:
        compute_direction(atab, dat)
    compute_score(screen, tl, dat, is_hyp)

    if is_hyp:
        if is_impl:
           insert_sort(screen, atab.hyp_impls, dat)
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
     
def update_autotab(screen, atab, dirty1, dirty2, interface, depth, defn=False):
    """
    Given an AutoTab data structure and a list of modified/added hypotheses
    (dirty1) and a list of modified/added targets (dirty2), update the data
    in the AutoTab structure to reflect current reality.
    """
    dirty1 = sorted(dirty1)
    dirty2 = sorted(dirty2)
    tlist0 = atab.tl.tlist0.data
    tlist1 = atab.tl.tlist1.data
    tlist2 = atab.tl.tlist2.data
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

            c1 = get_constants(screen, atab.tl, v.left)
            c2 = get_constants(screen, atab.tl, v.right)
            nc1 = get_constants(screen, atab.tl, complement_tree(v.left))
            nc2 = get_constants(screen, atab.tl, complement_tree(v.right))

            dat = AutoData(i, c1, c2, nc1, nc2)

            compute_direction(atab, dat)
            compute_score(screen, atab.tl, dat, True)

            m1 = metavars_used(v.left)
            m2 = metavars_used(v.right)
            mv = filter(lambda x : x not in m1, m2)
            nmv = filter(lambda x : x not in m2, m1)

            dat.mv_inc = len(list(mv))
            dat.nmv_inv = len(list(nmv))

            dat.defn = defn

            insert_sort(screen, atab.hyp_impls, dat)
        else:
            c = get_constants(screen, atab.tl, v)
            nc = get_constants(screen, atab.tl, complement_tree(v))

            dat = AutoData(i, c, None, nc, None)

            dat.deducts = deducts
            dat.depth = depth

            compute_score(screen, atab.tl, dat, True)

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

        c = get_constants(screen, atab.tl, v)
        nc = get_constants(screen, atab.tl, complement_tree(v))

        dat = AutoData(j, c, None, nc, None)

        dat.deducts = deducts

        compute_score(screen, atab.tl, dat, False)
        insert_sort(screen, atab.tar_heads, dat)

    atab.nhyps = len(tlist1)
    atab.ntars = len(tlist2)

    update_screen(screen, atab.tl, interface, dirty1, dirty2)

def autotab_remove_deadnodes(screen, atab, heads, impls, interface):
    list1 = atab.tl.tlist1.data
    list2 = atab.tl.tlist2.data
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

    return update_screen(screen, atab.tl, interface, sorted(dirty1), sorted(dirty2))

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
  
def create_index(screen, tl, library):
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

def filter_theorems1(screen, index, type_consts, consts):
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

def check_type_sizes(screen, tl, atab, n1, n2, interface):
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

def load_theorem(screen, atab, temp_tl, filepos, line):
    """
    Given a tableau and line where the theorem exist, copy the theorem into
    the main tableau if not already there and return the line where it is
    loaded.
    """
    tlist1 = atab.tl.tlist1.data
    dirty1 = []
    dirty2 = []
    
    if temp_tl != atab.tl: # theorem not already loaded
        # transfer library result to tableau
        j = len(tlist1)
        line += j # line in the main tableau where the theorem will be copied
        temp_tlist0 = temp_tl.tlist0.data
        temp_tlist1 = temp_tl.tlist1.data
        if temp_tlist0: # copy data across
            append_quantifiers(atab.tl.tlist0.data, temp_tlist0[0])
        for k in range(len(temp_tlist1)):
            append_tree(tlist1, temp_tlist1[k], dirty1)
        atab.libthms_loaded[filepos] = j # mark theorem as loaded
        atab.tl.vars = temp_tl.vars # update vars in main tableau
        atab.tl.stree = temp_tl.stree # update sort graph in main tableau
            
    return dirty1, dirty2, line

def temp_load_theorem(screen, atab, filepos, line):
    temp_tl = TreeList() # create a temporary tableau
    temp_tl.vars = deepcopy(atab.tl.vars) # copy variable subscript record from tl
    temp_tl.stree = atab.tl.stree # copy sort tree from tl
    sorts_mark(screen, atab.tl) # allow rollback of sort graph
    logic.library_import(screen, temp_tl, atab.library, filepos) # load the theorem into temporary tableau
    autocleanup(screen, temp_tl, TargetNode(-1, [])) # expand theorem into tableau with temporary target tree

    return temp_tl

def backwards_reasoning_possible(screen, atab, line2, filepos, line):
    """
    Given a filepos and line of a library result, check whether it applies to
    target with index line2 in the tableau. The return result is a triple
    (unifies1, unifies2, unifies3), the components of which specify whether
    the theorem applies with modus ponens, modus tollens or rewriting.
    """
    unifies1 = False
    unifies2 = False
    unifies3 = False

    tlist1 = atab.tl.tlist1.data
    tlist2 = atab.tl.tlist2.data

    if filepos in atab.libthms_loaded: # check if already loaded in tableau
        tl = atab.tl
        line += atab.libthms_loaded[filepos] # get position where it is loaded in tableau
        tnode = get_autonode(screen, atab.hyp_impls, line) # get the autonode for the theorem
        if tnode and line2 not in tnode.applied: # check we haven't already applied this theorem to this head
            tnode.applied.append(line2) # mark it as applied
            thm = tlist1[line] # theorem we are applying
            thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
            if isinstance(thm, ImpliesNode): # reasoning
                thm, _ = relabel(screen, tl, univs, thm, True)
                prec, u = unquantify(screen, thm.right, False)
                if not isinstance(prec, AndNode):
                    # check if precedent unifies with hyp
                    unifies1, assign, macros = unify(screen, tl, prec, tlist2[line2]) # check modus ponens
                if not unifies1:
                    prec, u = unquantify(screen, thm.left, True)
                    if not isinstance(prec, AndNode):
                        # check if precedent unifies with hyp
                        unifies2, assign, macros = unify(screen, tl, complement_tree(prec), tlist2[line2]) # check modus tollens
            elif isinstance(thm, EqNode): # rewriting
                unifies3, _, _ = logic.limited_equality_substitution(screen, atab.tl, atab.ttree, None, \
                                                                line, line2, False, True) # check rewriting
    else: # library theorem not yet loaded, load into temporary tableau
        temp_tl = temp_load_theorem(screen, atab, filepos, line)

        thm = temp_tl.tlist1.data[line] # line of interest in theorem in temporary tableau
        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
        thm, _ = relabel(screen, temp_tl, univs, thm, True)

        if isinstance(thm, ImpliesNode): # reasoning
            prec, u = unquantify(screen, thm.right, False)
            # check theorem has only one precedent
            if not isinstance(prec, AndNode):
                # check if precedent unifies with hyp
                unifies1, assign, macros = unify(screen, temp_tl, prec, tlist2[line2]) # check modus ponens
            if not unifies1:
                prec, u = unquantify(screen, thm.left, True)
                unifies2, assign, macros = unify(screen, temp_tl, complement_tree(prec), tlist2[line2]) # check modus tollens
        elif isinstance(thm, EqNode): # rewriting
            temp_list2 = temp_tl.tlist2.data
            temp_list2.append(tlist2[line2]) # append target to temporary tableau
            n = len(temp_list2) - 1
            unifies3, _, _ = logic.limited_equality_substitution(screen, temp_tl, atab.ttree, None, \
                                                            line, n, False, True) # check rewriting
            del temp_list2[n] # remove target from temporary tableau
        
        if not unifies1 and not unifies2 and not unifies3:
            sorts_rollback(screen, atab.tl) # restore sort graph if temporary tableau was loaded

        tl = temp_tl

    return unifies1, unifies2, unifies3, tl, line
    
def forwards_reasoning_possible(screen, atab, imp, hyp, mv_check, var_check, allow_ltor_violation):
    """
    Given a theorem node imp, check whether it applies to hypothesis with node
    hyp. The return result is a triple (unifies1, unifies2, unifies3), the
    components of which specify whether the theorem applies with modus ponens,
    modus tollens or rewriting.
    """
    unifies1 = False
    unifies2 = False
    unifies3 = False

    tlist1 = atab.tl.tlist1.data
    tlist2 = atab.tl.tlist2.data

    line1 = imp.line
    line2 = hyp.line

    if var_check:
        v1 = vars_used(screen, atab.tl, tlist1[line1])
        v2 = vars_used(screen, atab.tl, tlist1[line2])
                            
    if not var_check or v1 or v2:
        thm = tlist1[line1] # theorem we are applying
        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
        
        hc = hyp.const1

        pos = set(imp.const1).issubset(hc) and (not mv_check or imp.mv_inc == 0) and (imp.ltor or allow_ltor_violation)
        neg = set(imp.nconst2).issubset(hc) and imp.nmv_inc == 0 and (imp.rtol or allow_ltor_violation)

        if pos or neg:                
            if isinstance(thm, ImpliesNode): # reasoning
                if pos:
                    prec, u = unquantify(screen, thm.left, True)
                    if not isinstance(prec, AndNode):
                        # check if precedent unifies with hyp
                        unifies1, assign, macros = unify(screen, atab.tl, prec, tlist1[line2]) # check modus ponens
                if neg:
                    prec, u = unquantify(screen, thm.right, True)
                    if not isinstance(prec, AndNode):
                        # check if precedent unifies with hyp
                        comp = complement_tree(prec)
                        unifies2, assign, macros = unify(screen, atab.tl, comp, tlist1[line2]) # check modus tollens
            elif isinstance(thm, EqNode): # rewriting
                unifies3, _, _ = logic.limited_equality_substitution(screen, atab.tl, atab.ttree, None, \
                                                                line1, line2, True, True) # check rewriting

    return unifies1, unifies2, unifies3

def library_forwards_reasoning_possible(screen, atab, line2, filepos, line, mv_check, var_check):
    unifies1 = False
    unifies2 = False
    unifies3 = False

    tlist1 = atab.tl.tlist1.data
    tlist2 = atab.tl.tlist2.data
              
    if filepos in atab.libthms_loaded: # check if already loaded in tableau
        temp_tl = None
    else:
        temp_tl = temp_load_theorem(screen, atab, filepos, line)

        thm = temp_tl.tlist1.data[line] # line of interest in theorem in temporary tableau
        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars

        if isinstance(thm, ImpliesNode):
            if mv_check:
                m1 = metavars_used(thm.left)
                m2 = metavars_used(thm.right)
                mv = filter(lambda x : x not in m1, m2)
                nmv = filter(lambda x : x not in m2, m1)
                mv_inc = len(list(mv))
                nmv_inc = len(list(nmv))

                prec, u = unquantify(screen, thm.left, True)
                if not isinstance(prec, AndNode) and (not mv_check or mv_inc == 0):
                    # check if precedent unifies with hyp
                    if var_check:
                        v1 = vars_used(screen, atab.tl, prec)
                        v2 = vars_used(screen, atab.tl, tlist1[line2])
                    
                    if not var_check or v1 or v2: # ensure not applying metavar thm to metavar head
                        unifies1, assign, macros = unify(screen, temp_tl, prec, tlist1[line2])
                        if not unifies1:
                            prec, u = unquantify(screen, thm.right, False)
                            if not isinstance(prec, AndNode) and (not mv_check or nmv_inc == 0):
                                # check if precedent unifies with hyp
                                if var_check:
                                    v1 = vars_used(screen, atab.tl, prec)
                                    v2 = vars_used(screen, atab.tl, tlist1[line2])
                                        
                                if not var_check or v1 or v2: # ensure not applying metavar thm to metavar head
                                    unifies2, assign, macros = unify(screen, temp_tl, complement_tree(prec), tlist1[line2])
        elif isinstance(thm, EqNode):
            temp_tlist1 = temp_tl.tlist1.data
            temp_tlist1.append(tlist1[line2])
            n = len(temp_tlist1) - 1
            unifies3, _, _ = logic.limited_equality_substitution(screen, temp_tl, atab.ttree, None, line, n, True, True)
            del temp_tlist1[n]

        if not unifies1 and not unifies2 and not unifies3:
            sorts_rollback(screen, atab.tl) # restore sort graph if temporary tableau was loaded

    return unifies1, unifies2, unifies3, temp_tl, line

def apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, is_hyp):
    """
    Attempt to apply the theorem on line1 of the hypotheses to the head at line2.
    If is_hyp = True then the head is a hypothesis, otherwise it is a target.
    """
    tlist1 = atab.tl.tlist1.data
    tlist2 = atab.tl.tlist2.data

    # compute target dependency information
    dep = atab.tl.tlist1.dependency(line1)
    dep = target_compatible(screen, atab.tl, atab.ttree, dep, line2, is_hyp)
    
    if not dep: # not target compatible
        return False, None, None
    else: # target compatible
        if unifies1: # modus ponens
           return logic.modus_ponens(screen, atab.tl, atab.ttree, dep, line1, [line2], is_hyp)
        elif unifies2: # modus tollens
            return logic.modus_tollens(screen, atab.tl, atab.ttree, dep, line1, [line2], is_hyp)
        elif unifies3: # rewriting
            return logic.limited_equality_substitution(screen, atab.tl, atab.ttree, dep, line1, line2, is_hyp, False)
                                        
def check_done(screen, atab, interface):
    dirty1, dirty2, done, plist = check_targets_proved(screen, atab.tl, atab.ttree, atab.start1, atab.start2)

    atab.start1 = len(atab.tl.tlist1.data)
    atab.start2 = len(atab.tl.tlist2.data)
    
    update_screen(screen, atab.tl, interface, dirty1, dirty2)

    return done

def automate(screen, tl, ttree, interface='curses'):
    global automation_limit

    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data

    library = open("library.dat", "r")
    index, constants, undefined = create_index(screen, tl, library)
    
    atab = AutoTab(screen, tl, ttree, library, constants) # initialise automation data structure

    done = False # whether all targets are proved
    
    tar_heads_exhausted = [] # heads for which we've already tried everything
    hypc = []
    old_hypc = []
    for allow_ltor_violation in range(2):
        while True: # keep going until theorem proved or progress stalls
            progress = False

            hyp_heads_exhausted = [] # heads for which we've already tried everything
            old_hypc = hypc
            hypc = []

            for v in atab.hyp_heads:
                hypc = list_merge(hypc, v.const1)

            for v in atab.hyp_impls:
                c = list_merge(v.const1, v.const2)
                hypc = list_merge(hypc, c)

            if any(c not in old_hypc for c in hypc):
                tar_heads_exhausted = []

            for tar in atab.tar_heads:
                hprogress = False # whether some progress is made on the hypothesis side
                tprogress = False # whether some progress is made on the target side

                i = tar.line

                # find all target compatible hypotheses
                heads = [] # list of autonodes for target compatible hyp_heads
                impls = [] # list of autonodes for target compatible hyp_impls
                tarc = tar.const1

                for v in atab.hyp_heads:
                    if deps_compatible(screen, tl, ttree, i, v.line):
                        insert_sort(screen, heads, v)

                for v in atab.hyp_impls:
                    if deps_compatible(screen, tl, ttree, i, v.line):
                        insert_sort(screen, impls, v)

                # 1) first see if there are any theorems/defns to load which are not implications
                libthms = filter_theorems3(screen, index, hypc, tarc)
                for (title, c, nc, filepos, line) in libthms:
                    headc = c[2][line] # constants for this head

                    # check to see if constants of libthm are among the hyp constants hypc
                    if set(headc).issubset(hypc):
                        # check to see if thm already loaded, if not, load it
                        if filepos not in atab.libthms_loaded:
                            progress = True # we made progress affecting tableau

                            logic.library_import(screen, tl, library, filepos)

                            n1 = len(tlist1) # any lines after this have been added
                            n2 = len(tlist1)      

                            j = len(tlist1) - 1
                            update_autotab(screen, atab, [j], [], interface, 0)
                            atab.libthms_loaded[filepos] = j

                            dirty1, dirty2 = autocleanup(screen, tl, ttree)
                            update_autotab(screen, atab, dirty1, dirty2, interface, 0)
                            update_screen(screen, tl, interface, dirty1, dirty2)

                            done = check_done(screen, atab, interface)
                                            
                            if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                library.close()
                                automation_limit += automation_increment
                                return False

                            if done:
                                library.close()
                                return True

                            screen.debug("New non-implication thm loaded")

                if isinstance(tlist2[tar.line], DeadNode):
                    break

                # 2) try to find a theorem that applies to the target
                if tar not in tar_heads_exhausted:
                    libthms = filter_theorems2(screen, index, tarc)
                    for (title, c, nc, filepos, line, defn) in libthms:
                        implc = c[2][line].left
                        nimplc = nc[2][line].right

                        # check to see if constants of libthm are among the hyp constants hypc
                        pos = set(implc).issubset(hypc)
                        neg = set(nimplc).issubset(hypc)

                        if (pos or neg or not hypc or not atab.hyp_impls or not atab.hyp_heads):
                            # check to see if thm already loaded
                            line2 = tar.line

                            unifies1, unifies2, unifies3, temp_tl, line = backwards_reasoning_possible(screen, \
                                                                                           atab, line2, filepos, line)

                            if unifies1 or unifies2 or unifies3:
                                dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line)

                                update_autotab(screen, atab, dirty1, dirty2, interface, 0, defn) # update autotab with new lines

                                thmnode = get_autonode(screen, atab.hyp_impls, line1) # get autonode for theorem we want to apply
                                thmnode.applied.append(tar.line) # mark theorem as applied to our target

                                n1 = len(tl.tlist1.data) # any lines added after these are new
                                n2 = len(tl.tlist2.data)

                                # apply theorem
                                var1 = metavars_used(tlist1[line1].left)
                                var2 = metavars_used(tlist1[line1].right)
                                # conditions on theorems/definitions we allow (more is possible for a definition)
                                if (defn and ((unifies1 and not set(thmnode.const2).issubset(thmnode.const1)) or \
                                            (unifies2 and not set(thmnode.const1).issubset(thmnode.const2)))) or \
                                   (unifies1 and set(var1).issubset(var2)) or \
                                   (unifies2 and set(var2).issubset(var1))  or \
                                   (unifies3):

                                    success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, False)
                                    if success:
                                        tar.deducts += 1
                                        adjust_score(screen, tl, atab, tar.line, False)

                                        update_autotab(screen, atab, dirty1, dirty2, interface, 0, defn)
                                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                        update_autotab(screen, atab, dirty1, dirty2, interface, 0, defn)
                                        update_screen(screen, tl, interface, dirty1, dirty2)

                                        # remove deductions which are duplicates or that have oversize types
                                        c1 = check_duplicates(screen, tl, ttree, n1, n2, i, interface)
                                        c2 = check_type_sizes(screen, tl, atab, n1, n2, interface)

                                        if c1 and c2:
                                            tprogress = True # we made progress that affected the tableau
                                            progress = True

                                            done = check_done(screen, atab, interface)
                                            
                                            if done:
                                                library.close()
                                                return True

                                            screen.debug("New target created")

                                        if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                            library.close()
                                            automation_limit += automation_increment
                                            return False

                                        if c1 and c2:
                                            break
                if tprogress:
                    break
                tar_heads_exhausted.append(tar)
                # 3) find all consequences of individual hypotheses (Fredy's ball)
                for hyp in heads:
                    if hyp in hyp_heads_exhausted:
                        continue

                    progress = False

                    line2 = hyp.line

                    ht = get_constants_qz(screen, tl, tl.tlist0.data[0]) if tl.tlist0.data else [] # type constants

                    # first check if any hyp_impls can be applied to head
                    for imp in impls:
                        if (imp.line, allow_ltor_violation) in hyp.applied: # check if we've applied this theorem before
                            continue

                        hyp.applied.append((imp.line, allow_ltor_violation)) # mark as applied

                        line1 = imp.line

                        unifies1, unifies2, unifies3 = \
                              forwards_reasoning_possible(screen, atab, imp, hyp, True, True, allow_ltor_violation)

                        if unifies1 or unifies2 or unifies3:
                            n1 = len(tl.tlist1.data) # any lines after this have been added to tableau
                                
                            # apply modus ponens and or modus tollens
                            success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, True)
                            if success:
                                hyp.deducts += 1
                                adjust_score(screen, tl, atab, hyp.line, True)
                                imp.deducts += 1
                                adjust_score(screen, tl, atab, imp.line, True)

                                update_autotab(screen, atab, dirty1, dirty2, interface, hyp.depth+1)
                                dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                update_autotab(screen, atab, dirty1, dirty2, interface, hyp.depth+1)
                                update_screen(screen, tl, interface, dirty1, dirty2)

                                # remove deductions which are duplicates or that have oversize types or that are trivial
                                c1 = check_duplicates(screen, tl, ttree, n1, len(tlist2), i, interface)
                                c2 = check_type_sizes(screen, tl, atab, n1, len(tlist2), interface)
                                c3 = check_trivial(screen, tl, atab, n1, interface)

                                if c1 and c2 and c3:
                                    hprogress = True # we have made progress affecting the tableau
                                    progress = True

                                    done = check_done(screen, atab, interface)
                                            
                                    if done:
                                        library.close()
                                        return True

                                    hyp_heads_exhausted = []
                                    tar_heads_exhausted = []
                                    screen.debug("New hypothesis deduced")

                                if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False

                                if c1 and c2 and c3:
                                    break
                    if hprogress:
                        break

                    # 4) no progress, look for library result that can be applied to head
                    libthms = filter_theorems1(screen, index, ht, hyp.const1)
                    for (title, c, nc, filepos, line, defn) in libthms:
                        if filepos < hyp.filepos_done or (filepos == hyp.filepos_done and line < hyp.line_done):
                            continue

                        hyp.filepos_done = filepos
                        hyp.line_done = line + 1

                        unifies1, unifies2, unifies3, temp_tl, line = library_forwards_reasoning_possible(screen, \
                                                                                  atab, line2, filepos, line, True, True)

                        if unifies1 or unifies2 or unifies3:
                            # transfer library result to tableau
                            hprogress = True # we made progress that affects the tableau
                            progress = True

                            dirty1, dirty2, line = load_theorem(screen, atab, temp_tl, filepos, line)

                            update_autotab(screen, atab, dirty1, dirty2, interface, hyp.depth + 1, defn)

                            screen.debug("New library result loaded")
                            break

                    if hprogress:
                        break

                    hyp_heads_exhausted.append(hyp)

                if hprogress:
                    break

            if not progress:
                break

    if not progress:
        # one final check that we are not done
        done = check_done(screen, atab, interface)
                                            
        if autotab_remove_deadnodes(screen, atab, None, None, interface):
            library.close()
            automation_limit += automation_increment
            return False
        
        if done:
            library.close()
            return True
        
        screen.debug("Final failure")
        return False


        