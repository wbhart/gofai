from utility import is_implication, get_constants, get_init_vars, list_merge, deps_compatible, \
     TargetNode, update_constraints, process_sorts, append_tree, unquantify, target_compatible, \
     append_quantifiers, relabel, deps_defunct, is_duplicate_upto_metavars, metavars_used, \
     vars_used, max_type_size, complement_tree, sorts_mark, sorts_rollback, is_equality, \
     target_depends, get_constants_qz, find_hydras, replace_tree, record_move, deps_intersect
from autoparse import parse_consts
from moves import check_targets_proved
from unification import unify, substitute
from nodes import DeadNode, AutoImplNode, AutoEqNode, AutoIffNode, ImpliesNode, AndNode, \
     SymbolNode, NeqNode, ForallNode, EqNode, NotNode, FnApplNode, SubsetneqNode, LeafNode, \
     LRNode, TupleNode, ExistsNode, OrNode, ElemNode, VarNode
from tree import TreeList
from interface import nchars_to_chars, iswide_char
from copy import deepcopy, copy
import logic, math

automation_limit     = 1000 # number of lines in hypothesis pane before automation gives up
automation_increment = 300 # number of lines to add next time automation is called

tab_count = 0

# Mode 0 : backwards reasoning only uses definitions, no metavars are allowed to be introduced in targets
# Mode 1 : backwards reasoning may use any implication, new metavars are allowed to be introduced in targets using definitions
# depth  : search depth on the hypothesis side

try:
    from flask import Flask, render_template
    from flask_socketio import SocketIO, emit
except:
    pass

class ConstGraphNode:
    def __init__(self, name):
        self.name = name
        self.descendants = [] # list of constants that are smaller than the current constant

def find_constant(top_list, name):
    """
    Find and return the node in the constant graph with the given name.
    """
    # first define a function to search one of the graphs using depth first search
    def find(node, name):
        if node.name == name: # we found the node
            return node
        
        for n in node.descendants:
            v = find(n, name) # depth first search
            if v:
                return v

        return None

    for n in top_list:
        v = find(n, name)
        if v:
            return v
    
    return None

def insert_constant(top_list, hiname, loname_list):
    """
    Given a list (top_list) of constant graphs, search for loname in the list and insert hiname
    above it in the list.
    """
    new_node = ConstGraphNode(hiname) # create a new node for the new constant
    removal_list = [] # list of nodes to remove

    # first find loname in the graph list
    for loname in loname_list:
        node = find_constant(top_list, loname)
    
        if not node:
            raise Exception("Node name not found in constant graph : "+loname)

        if node in top_list: # if it is at the top level, remove it
            removal_list.append(node)

        new_node.descendants.append(node)
    
    for node in removal_list: # remove all nodes we now dominate
        top_list.remove(node)

    top_list.append(new_node) # put the new node in the list

def constant_greater(constant_graph, c1, c2):
    """
    Return True if constant c1 is greater than c2. Note that incomparable constants
    will return False
    """
    node = find_constant(constant_graph, c1) # find c1 node

    if not node:
        raise Exception("Constant not found : "+c1)

    return find_constant(node.descendants, c2) != None # try to find c2 starting at c1

def check_maximal_constants(constant_graph, maximal_constants, constants):
    """
    Return True if none of the given constants is bigger than the current maximal constants.
    """
    for c in constants:
        for cmax in maximal_constants:
            if constant_greater(constant_graph, c, cmax):
                return False

    return True

def get_maximal_constants(constant_graph, tl):
    hyps = tl.tlist1.data # hypothesis list
    tars = tl.tlist2.data # target list

    constants = [] # list of all constants
    maximal_constants = [] # list of maximal constants we will compute

    for tree in hyps:
        constants = get_constants(None, None, tree, constants, False)

    for tree in tars:
        constants = get_constants(None, None, tree, constants, False)

    while constants: # iterate through all the constants
        c = constants.pop() # get next constant
        
        # first check if c is dominated by some existing maximal constant
        maximal = True
        for cmax in maximal_constants:
            if constant_greater(constant_graph, cmax, c):
                maximal = False # constant c is not maximal
                
        if maximal: # c is a new maximal constant
            # remove maximal constants dominated by c
            for m in maximal_constants:
                if constant_greater(constant_graph, c, m):
                    maximal_constants.remove(m)

            maximal_constants.append(c) # add the new maximal constant

    return maximal_constants

class AutoData:
    def __init__(self, line, const1, const2, nconst1, nconst2):
        self.line = line # line in the hypothesis or target pane
        self.const1 = const1 # constants on left side of implication or constants in predicate
        self.const2 = const2 # constants on right side of implication
        self.nconst1 = nconst1 # negated constants on left side of implication or constants in predicate
        self.nconst2 = nconst2 # negated constants on right side of implication
        self.applied = [] # list of impls that have been applies to this head
        self.applied2 = [] # list of heads that have been applied to this impl
        self.type_applied = [] # list of (varname, line) pairs of type judgements already obtained for this judgement
        self.type = False # whether this head is the result of a type judgement
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
        self.special = False # whether this node is a special theorem that is not an implication
        self.ancestors = [] # ancestors of this node as far as reasoning is concerned
        self.backtrackable = False # whether this node could still be backtracked

    def __str__(self):
        return str(self.line)

    def __repr__(self):
        return repr(self.line)

class AutoTab:
    def __init__(self, screen, tl, ttree, library, constants, constant_order):
        tlist0 = tl.tlist0.data
        tlist1 = tl.tlist1.data
        tlist2 = tl.tlist2.data
        global tab_count

        self.tl = tl
        self.ttree = ttree
        self.nhyps = len(tlist1)
        self.ntars = len(tlist2)
        self.libthms_loaded = dict() # keep track of which library theorems we loaded, and where
        self.library = library
        self.hydras = [] # list of current hydras
        self.hydra = None # current hydra
        self.start1 = 0 # for incremental completion checking
        self.start2 = 0
        self.constants = constants
        self.constant_order = constant_order
        self.hyps_active = [] # hypotheses still active in current tableau
        self.tars_active = [] # targets still active in current tableau
        self.hyp_list = [k for k in range(len(tlist1))] # list of hypotheses covered by this tableau
        self.tar_list = [k for k in range(len(tlist2))] # list of targets covered by this tableau
        self.descendants = [] # tableaus derived from this one (via splitting)
        self.top_tab = None # top tableau from which all others derived
        self.hyp_nodes = [] # list of all hypothesis nodes
        self.marked = False # used to prevent dealing with same atab multiple times
        self.num = tab_count
        tab_count += 1

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
                self.hyp_nodes.append(dat)

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
                self.hyp_nodes.append(dat)
                
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

def check_constant_direction(atab, const1, const2):
    max_l = -1
    max_r = -1
    for i in range(len(atab.constant_order)):
        c = atab.constant_order[i]
        if c in const1:
            max_l = i
        if c in const2:
            max_r = i
    return max_l >= max_r

def compute_direction(atab, dat):
    dat.ltor = check_constant_direction(atab, dat.const1, dat.const2)
    dat.rtol = check_constant_direction(atab, dat.nconst2, dat.nconst1)

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

        # don't insert duplicate
        i = lo
        while i < len(L) and L[i].score == dat.score:
            if L[i] == dat:
                return
            i += 1

        L.insert(lo, dat)
     
def unmark(atab):
    if atab.marked == False:
        return
    
    atab.marked = False

    for tab in atab.descendants:
        if tab.marked:
            unmark(tab)

def update_tabs(screen, atab, new_tab, dirty1, dirty2, line, descendant=False):
    tlist1 = new_tab.tl.tlist1.data
    # if len(atab.tl.tlist1.data) != len(tlist1):
    for i in dirty1:
        if line == None or i != line or descendant:
            if i < len(atab.tl.tlist1.data):
                atab.tl.tlist1.data[i] = deepcopy(tlist1[i])
            else:
                atab.tl.tlist1.data.append(deepcopy(tlist1[i]))
            
    tlist2 = new_tab.tl.tlist2.data
    # if len(atab.tl.tlist2.data) != len(tlist2):
    for i in dirty2:
        if i < len(atab.tl.tlist2.data):
            atab.tl.tlist2.data[i] = deepcopy(tlist2[i])
        else:
            atab.tl.tlist2.data.append(deepcopy(tlist2[i]))

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            update_tabs(screen, tab, new_tab, dirty1, dirty2, line, descendant or atab==new_tab)

def update_lists(screen, atab, dirty1, dirty2):
    for i in dirty1:
        if i not in atab.hyp_list:
            atab.hyp_list.append(i)

    for i in dirty2:
        if i not in atab.tar_list:
            atab.tar_list.append(i)

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            update_lists(screen, tab, dirty1, dirty2)

def get_paths(screen, ttree, dirty2):
    paths = [] # paths to nodes in dirty2
    
    def find(ttree, dirty2, current_path=[]):
        current_path.append(ttree)
        
        if ttree.num in dirty2:
            paths.append(copy(current_path))
        
        for node in ttree.andlist:
            find(node, dirty2, current_path)

        current_path.pop()

    find(ttree, dirty2)

    return paths

def update_ttrees(screen, atab, paths):
    
    orig_ttree = atab.ttree

    for path in paths:
        ttree = atab.ttree
        
        for node in path:
            if node.num != -1:
                found = False

                for t in ttree.andlist:
                    if t.num == node.num:
                        ttree = t
                        found = True
                        break

                if not found:
                    node_copy = copy(node)
                    node_copy.proved = False
                    node_copy.andlist = []
                    ttree.andlist.append(node_copy)
                    ttree = node_copy
  
    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            update_ttrees(screen, tab, paths)

def update_hyp_tar_tabs(screen, atab, new_tab, dirty1, dirty2, line, descendant=False):
    for i in dirty1:
        if line == None or i != line or descendant:
            if i < len(atab.tl.hyp_tab):
                atab.tl.hyp_tab[i] = new_tab
            elif i == len(atab.tl.hyp_tab):
                atab.tl.hyp_tab.append(new_tab)
            else:
                for j in range(len(atab.tl.hyp_tab), i - 1):
                    atab.tl.hyp_tab.append(None)
                atab.tl.hyp_tab.append(new_tab)
    
    for i in dirty2:
        if i < len(atab.tl.tar_tab):
            atab.tl.tar_tab[i] = new_tab
        elif i == len(atab.tl.tar_tab):
            atab.tl.tar_tab.append(new_tab)
        else:
            for j in range(len(atab.tl.tar_tab), i - 1):
                atab.tl.tar_tab.append(None)
            atab.tl.tar_tab.append(new_tab)

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            update_hyp_tar_tabs(screen, tab, new_tab, dirty1, dirty2, line, descendant or atab==new_tab)

def update_autotab(screen, orig_tab, atab, dirty1, dirty2, interface, depth, \
                                defn=False, special=False, library=False, top=True, \
                                hhead_dats0=None, himpl_dats0=None, thead_dats0=None, split_line=None):
    """
    Given an AutoTab data structure and a list of modified/added hypotheses
    (dirty1) and a list of modified/added targets (dirty2), update the data
    in the AutoTab structure to reflect current reality.
    """
    if top:
        hhead_dats = []
        himpl_dats = []
        thead_dats = []

        dirty1 = list(sorted(dirty1))
        dirty2 = list(sorted(dirty2))

        update_hyp_tar_tabs(screen, atab.top_tab, atab, dirty1, dirty2, split_line)
        unmark(atab.top_tab)
        update_tabs(screen, atab.top_tab, orig_tab, dirty1, dirty2, split_line)
        unmark(atab.top_tab)
        update_tabs(screen, orig_tab, orig_tab, dirty1, dirty2, split_line)
        unmark(orig_tab)
        update_lists(screen, atab, dirty1, dirty2)
        unmark(atab)
        paths = get_paths(screen, orig_tab.ttree, dirty2)
        update_ttrees(screen, atab, paths)
        unmark(atab)
    else:
       hhead_dats = hhead_dats0
       himpl_dats = himpl_dats0
       thead_dats = thead_dats0

    tlist0 = atab.tl.tlist0.data
    tlist1 = atab.tl.tlist1.data
    tlist2 = atab.tl.tlist2.data

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
        for dat in atab.hyps_active:
            if dat.line == i:
                atab.hyps_active.remove(dat)
        # add new details
        atab.start1 = min(atab.start1, i)

    if top:
        for i in dirty1:
            v = tlist1[i]
            
            if is_implication(v) or is_equality(v):
                v, univs = unquantify(screen, v, False)

                c1 = get_constants(screen, atab.tl, v.left)
                c2 = get_constants(screen, atab.tl, v.right)
                nc1 = get_constants(screen, atab.tl, complement_tree(v.left))
                nc2 = get_constants(screen, atab.tl, complement_tree(v.right))

                dat = AutoData(i, c1, c2, nc1, nc2)
                atab.hyp_nodes.append(dat)

                compute_direction(atab, dat)
                compute_score(screen, atab.tl, dat, True)

                m1 = metavars_used(v.left)
                m2 = metavars_used(v.right)
                mv = filter(lambda x : x not in m1, m2)
                nmv = filter(lambda x : x not in m2, m1)

                dat.mv_inc = len(list(mv))
                dat.nmv_inv = len(list(nmv))

                dat.defn = defn
                himpl_dats.append(dat)
            else:
                c = get_constants(screen, atab.tl, v)
                nc = get_constants(screen, atab.tl, complement_tree(v))
                
                dat = AutoData(i, c, None, nc, None)
                atab.hyp_nodes.append(dat)

                if special:
                    dat.special = True
                
                dat.depth = depth

                compute_score(screen, atab.tl, dat, True)

                hhead_dats.append(dat)

    for dat in hhead_dats:
        if not library:
            atab.hyps_active.append(dat)

        insert_sort(screen, atab.hyp_heads, dat)

    for dat in himpl_dats:
        if not library:
            atab.hyps_active.append(dat)
        
        insert_sort(screen, atab.hyp_impls, dat) 

    for j in dirty2:
        if j < atab.ntars: # delete old target
            k = 0
            while k < len(atab.tar_heads):
                t = atab.tar_heads[k]
                if t.line == j:
                    del atab.tar_heads[k]
                else:
                    k += 1

        for dat in atab.tars_active:
            if dat.line == j:
                atab.tars_active.remove(dat)

        atab.start2 = min(atab.start2, j)

    if top:
        for j in dirty2:
            # add new details
            v = tlist2[j]

            c = get_constants(screen, atab.tl, v)
            nc = get_constants(screen, atab.tl, complement_tree(v))

            dat = AutoData(j, c, None, nc, None)
            
            compute_score(screen, atab.tl, dat, False)
            
            thead_dats.append(dat)

    for dat in thead_dats:
        atab.tars_active.append(dat)

        insert_sort(screen, atab.tar_heads, dat)

    atab.nhyps = len(tlist1)
    atab.ntars = len(tlist2)

    if atab == orig_tab:
        update_screen(screen, atab, interface, dirty1, dirty2)

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            update_autotab(screen, orig_tab, tab, dirty1, dirty2, interface, depth, \
                         defn, special, library, False, hhead_dats, himpl_dats, thead_dats)

    if top:
        unmark(atab)
        return hhead_dats + himpl_dats, thead_dats

def autotab_remove_deadnodes(screen, atab, heads, impls, interface, top=True):
    list1 = atab.tl.tlist1.data
    list2 = atab.tl.tlist2.data
    dirty1 = []
    dirty2 = []
    j = 0
    while j < len(atab.hyp_heads):
        if isinstance(list1[atab.hyp_heads[j].line], DeadNode):
            if top:
                dirty1.append(atab.hyp_heads[j].line)
            del atab.hyp_heads[j]
        else:
            j += 1
    j = 0
    while j < len(atab.hyp_impls):
        if isinstance(list1[atab.hyp_impls[j].line], DeadNode):
            if top:
                dirty1.append(atab.hyp_impls[j].line)
            del atab.hyp_impls[j]
        else:
            j += 1
    j = 0
    while j < len(atab.tar_heads):
        if isinstance(list2[atab.tar_heads[j].line], DeadNode):
            if top:
                dirty2.append(atab.tar_heads[j].line)
            del atab.tar_heads[j]
        else:
            j += 1
    j = 0
    while j < len(atab.hyps_active):
        if isinstance(list1[atab.hyps_active[j].line], DeadNode):
            del atab.hyps_active[j]
        else:
            j += 1
    j = 0
    while j < len(atab.tars_active):
        if isinstance(list2[atab.tars_active[j].line], DeadNode):
            del atab.tars_active[j]
        else:
            j += 1
    if top:
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

    #for tab in atab.descendants:
    #    autotab_remove_deadnodes(screen, tab, heads, impls, interface, False)

    if top:
        return update_screen(screen, atab, interface, sorted(dirty1), sorted(dirty2))

def is_definition(screen, constants, defined, consts, nconsts):
    """
    Determine whether the theorems listed in consts define new symbols and if
    so add them to the constants graph. If the symbols are used for the first
    time but undefined also insert them in the constant graph list. Return True
    if the given theorems form a definition.
    """
    const_list = [] # list of constants occurring that are not being defined
    t_heads = consts[1]
    thmlist = consts[2]
    nthmlist = nconsts[2]
    # check if the t_head defines a new symbol
    is_defn = False
    for c in t_heads:
        if not find_constant(constants, c):
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
                if c not in defined:
                    defined.append(c) # this constant is new and is being defined
                is_defn = True
            else:
                constants.append(ConstGraphNode(c)) # insert as undefined constant

    for thm in thmlist:
        if isinstance(thm, AutoEqNode) or isinstance(thm, AutoIffNode) or \
            isinstance(thm, AutoImplNode):
                for c in thm.left:
                    if not find_constant(constants, c):
                        if c not in thm.right:
                            if c not in defined:
                                defined.append(c)
                            is_defn = True
                        else:
                            if c not in const_list:
                                constants.append(ConstGraphNode(c)) # insert as undefined constant
                                const_list.append(c)
                    else:
                        if c not in const_list:
                            const_list.append(c)
                for c in thm.right:
                    if c not in const_list:
                        const_list.append(c)
                    if not find_constant(constants, c):
                        constants.append(ConstGraphNode(c)) # insert as undefined constant
        else:
            for c in thm:
                if not find_constant(constants, c):
                    is_defn = True
                    if c not in defined:
                        defined.append(c)
                else:
                    if c not in const_list:
                         const_list.append(c)
                        

    for thm in nthmlist:
        if isinstance(thm, AutoEqNode) or isinstance(thm, AutoIffNode) or \
            isinstance(thm, AutoImplNode):
                for c in thm.left:
                    if not find_constant(constants, c):
                        if c not in thm.right:
                            if c not in defined:
                                defined.append(c)
                            is_defn = True
                        else:
                            if c not in const_list:
                                constants.append(ConstGraphNode(c)) # insert as undefined constant
                                const_list.append(c)
                    else:
                        if c not in const_list:
                            const_list.append(c)
                for c in thm.right:
                    if c not in const_list:
                        const_list.append(c)
                    if not find_constant(constants, c):
                        constants.append(ConstGraphNode(c)) # insert as undefined constant
        else:
            for c in thm:
                if not find_constant(constants, c):
                    is_defn = True
                    if c not in defined:
                        defined.append(c)
                else:
                    if c not in const_list:
                         const_list.append(c)

    for c in defined: # removed newly defined constants from list of undefined constants
        if c in const_list:
            const_list.remove(c)

    for c in defined:
        insert_constant(constants, c, const_list)

    return is_defn
  
def create_index(screen, tl, library):
    """
    Read the library in and create an index of all theorems and definitions up
    to but not including the theorem we are trying to prove.
    """
    constant_graph = [] # a list of root nodes of constant graphs
    constant_order = [] # a list of constants in the order they are defined
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
            defn = is_definition(screen, constant_graph, constant_order, consts, nconsts)
            index.append((title, consts, nconsts, filepos, defn))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    return index, constant_graph, constant_order

def get_autonode(screen, alist, line):
    for node in alist:
        if node.line == line:
            return node

    return None

def filter_theorems1(screen, index, type_consts, consts, tabc):
    """
    Given a library index, filter out theorems all of whose precedents
    contain only constants in the given list and whose type constants
    are all contained in the given list and which doesn't introduce
    new constants not in the tableau, the list of which is given by
    tabc.
    """
    thms = []

    for (title, c, nc, filepos, defn) in index:
        if not defn:
            thmlist = c[2]
            nthmlist = nc[2]
            tconst = c[0]

            for line in range(len(thmlist)):
                thm = thmlist[line]
                nthm = nthmlist[line]

                if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode):
                    tc = thm.left
                    tcr = thm.right
                    tnc = nthm.right
                    tncl = nthm.left
                    yes = title == 'Extensionality of sets'
                    if set(tconst).issubset(type_consts):
                        if set(tc).issubset(consts):
                            if set(tcr).issubset(tc) or not set(tc).issubset(tcr):
                                if set(tcr).issubset(tabc):
                                    thms.append((title, True, False, filepos, line))
                        if set(tnc).issubset(consts):
                            if set(tncl).issubset(tnc) or not set(tnc).issubset(tncl):
                                if set(tncl).issubset(tabc):
                                    thms.append((title, False, True, filepos, line))
    return thms

def filter_theorems2(screen, atab, index, consts, hypc):
    """
    Given a library index, filter out theorems all of whose consequents
    contain only constants in the given list and which won't introduce new
    constants not in the hypotheses, the list of which is given by hypc.
    """
    thms = []
    
    for (title, c, nc, filepos, defn) in index:
        if not defn:
            thmlist = c[2]
            nthmlist = nc[2]

            for line in range(len(thmlist)):
                thm = thmlist[line]
                nthm = nthmlist[line]

                if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode):
                    tc = thm.right
                    tcl = thm.left
                    tnc = nthm.left
                    tncr = nthm.right

                    if set(tc).issubset(consts):
                        if set(tcl).issubset(tc) or not set(tc).issubset(tcl):
                            if set(tcl).issubset(hypc): # ensure we don't add new constants to hypotheses
                                thms.append((title, True, False, filepos, line))

                    if set(tnc).issubset(consts):
                        if set(tncr).issubset(tnc) or not set(tnc).issubset(tncr):
                            if set(tncr).issubset(hypc): # ensure we don't add new constants to hypotheses
                                thms.append((title, False, True, filepos, line))
    return thms

def filter_theorems3(screen, index, consts):
    """
    Given a library index, filter out theorems which are heads that
    contain only constants in the given list.
    """
    thms = []

    for (title, c, nc, filepos, defn) in index:
        thmlist = c[2]

        for line in range(len(thmlist)):
            thm = thmlist[line]

            if not isinstance(thm, AutoImplNode) and not isinstance(thm, AutoEqNode) and \
               not isinstance(thm, AutoIffNode):
                if set(thm).issubset(consts):
                    thms.append((title, filepos, line))
    return thms

def filter_implications1(screen, atab, impls, consts):
    """
    Given a list of constants and a list of implication nodes, filter out those that
    could apply to a target with the given consts.
    """
    impl_list = []

    for impl in impls:
        imp = atab.tl.tlist1.data[impl.line]

        var1 = metavars_used(imp.left)
        var2 = metavars_used(imp.right)
                    
        if set(impl.const2).issubset(consts) and impl.rtol: # may match given consts
            if set(impl.const1).issubset(impl.const2) or not set(impl.const2).issubset(impl.const1):
                if set(var1).issubset(var2):
                    impl_list.append((impl, True, False))

        if set(impl.nconst1).issubset(consts) and impl.ltor: # may match given consts
            if set(impl.nconst2).issubset(impl.nconst1) or not set(impl.nconst1).issubset(impl.nconst2):
                if set(var2).issubset(var1):
                    impl_list.append((impl, False, True))

    return impl_list

def filter_implications2(screen, atab, impls, consts, special=False):
    """
    Given a list of constants and a list of implication nodes, filter out those that
    could apply to a head with the given consts.
    """
    impl_list = []

    for impl in impls:
        imp = atab.tl.tlist1.data[impl.line]
        pos = False
        neg = False

        var1 = metavars_used(imp.left)
        var2 = metavars_used(imp.right)
                    
        if set(impl.const1).issubset(consts) and (special or impl.ltor): # may match given consts
            if special or set(impl.const2).issubset(impl.const1) or not set(impl.const1).issubset(impl.const2):
                if special or set(var2).issubset(var1):
                    pos = True

        if set(impl.nconst2).issubset(consts) and (special or impl.rtol): # may match given consts
            if special or set(impl.nconst1).issubset(impl.nconst2) or not set(impl.nconst2).issubset(impl.nconst1):
                if special or set(var1).issubset(var2):
                    neg = True
        
        if pos or neg:
            impl_list.append((impl, pos, neg))

    return impl_list

def is_type_judgement(title):
    if title == 'Definition of set universe':
        return True
    
    return False
    
def filter_judgements1(screen, index, type_consts, consts, tabc, library=False):
    """
    Given a library index, filter out definitions all of whose precedents
    contain only constants in the given list and whose type constants
    are all contained in the given list.
    """
    thms = []

    for (title, c, nc, filepos, defn) in index:
        if is_type_judgement(title):
            thmlist = c[2]
            nthmlist = nc[2]
            tconst = c[0]

            for line in range(len(thmlist)):
                thm = thmlist[line]
                nthm = nthmlist[line]

                if isinstance(thm, AutoImplNode):
                    tc = thm.left
                    tcr = thm.right
                    tnc = nthm.right
                    tncl = nthm.left
                    
                    if set(tconst).issubset(type_consts):
                        if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode):
                            if set(tc).issubset(consts):
                                if library or set(tcr).issubset(tabc):
                                    thms.append((title, True, False, filepos, line))

    return thms

def filter_definitions1(screen, atab, index, type_consts, consts, tabc, library=False):
    """
    Given a library index, filter out definitions all of whose precedents
    contain only constants in the given list and whose type constants
    are all contained in the given list.
    """
    thms = []

    for (title, c, nc, filepos, defn) in index:
        if defn and not is_type_judgement(title):
            thmlist = c[2]
            nthmlist = nc[2]
            tconst = c[0]

            for line in range(len(thmlist)):
                thm = thmlist[line]
                nthm = nthmlist[line]

                if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode) or isinstance(thm, AutoEqNode):
                    tc = thm.left
                    tcr = thm.right
                    tnc = nthm.right
                    tncl = nthm.left
                    
                    if set(tconst).issubset(type_consts):
                        if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode):
                            if set(tc).issubset(consts) and check_constant_direction(atab, tc, tcr):
                                if library or set(tcr).issubset(tabc):
                                    thms.append((title, True, False, False, filepos, line))
                            if set(tnc).issubset(consts) and check_constant_direction(atab, tnc, tncl):
                                if library or set(tncl).issubset(tabc):
                                    thms.append((title, False, True, False, filepos, line))
                        else: # AutoEqNode
                            if set(tc).issubset(consts):
                                if library or (set(tcr).issubset(tabc) and check_constant_direction(atab, tc, tcr)):
                                    thms.append((title, False, False, True, filepos, line))

    return thms

def filter_definitions2(screen, atab, index, consts, hypc, library=False):
    """
    Given a library index, filter out definition all of whose consequents
    contain only constants in the given list.
    """
    thms = []

    # we allow backwards reasoning if there are no hyp_heads
    empty = not hypc or not atab.hyp_heads
    
    for (title, c, nc, filepos, defn) in index:
        if defn:
            thmlist = c[2]
            nthmlist = nc[2]

            for line in range(len(thmlist)):
                thm = thmlist[line]
                nthm = nthmlist[line]

                if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode) or isinstance(thm, AutoEqNode):
                    tc = thm.right
                    tcl = thm.left
                    tnc = nthm.left
                    tncr = nthm.right
                    
                    if isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode):
                        if set(tc).issubset(consts) and check_constant_direction(atab, tc, tcl):
                            if library or empty or set(tcl).issubset(hypc):
                                thms.append((title, True, False, False, filepos, line))

                        if set(tnc).issubset(consts) and check_constant_direction(atab, tnc, tncr):
                            if library or empty or set(tncr).issubset(hypc): # ensure we don't add new constants to hypotheses
                                thms.append((title, False, True, False, filepos, line))
                    else: # AutoEqNode
                        if set(tcl).issubset(consts) and check_constant_direction(atab, tcl, tc):
                            if library or empty or set(tc).issubset(hypc):
                                thms.append((title, False, False, True, filepos, line))                
    return thms

def filter_definitions3(screen, atab, index, type_consts, const1, const2, tabc):
    """
    Given a library index, filter out definitions all of whose precedents
    contain only constants in one of the given lists (the second list may
    optionally be None) and whose type constants are all contained in the
    given list.
    """
    thms = []

    for (title, c, nc, filepos, defn) in index:
        if defn:
            thmlist = c[2]
            nthmlist = nc[2]
            tconst = c[0]

            for line in range(len(thmlist)):
                thm = thmlist[line]
                nthm = nthmlist[line]

                if isinstance(thm, AutoIffNode):
                    tc = thm.left
                    tcr = thm.right
                    
                    if set(tconst).issubset(type_consts):
                        set_tc = set(tc)
                        if set_tc.issubset(const1) or const2 == None or set_tc.issubset(const2):
                            if set(tcr).issubset(tabc):
                                thms.append((title, filepos, line))

    return thms

def autocleanup(screen, tl, ttree, defn=False):
    dirty1, dirty2 = logic.cleanup(screen, tl, ttree, defn)
    logic.fill_macros(screen, tl)
    ok, error = update_constraints(screen, tl)
    if ok:
        ok, error = process_sorts(screen, tl)
        if not ok:
            screen.dialog(error)
    else:
        screen.dialog(error)
    return dirty1, dirty2

def clear_screen(screen, tl, interface):
    global automation_limit
    if interface == 'curses':
        pad1 = screen.pad1.pad
        pad2 = screen.pad2.pad
        screen.pad0.pad[0] = ''
        for i in range(automation_limit):
            pad1[i] = ''
            pad2[i] = ''
        screen.pad1.scroll_line = 0
        screen.pad1.cursor_line = 0
        screen.pad2.scroll_line = 0
        screen.pad2.cursor_line = 0
        tl.tlist1.line = 0
        tl.tlist2.line = 0
        screen.pad0.refresh()
        screen.pad1.refresh()
        screen.pad2.refresh()
        screen.focus.refresh()
    else:
        raise Exception("clear_screen not implemented for javascript interface")

def update_screen(screen, atab, interface, d1=None, d2=None):
    global automation_limit
    tl = atab.tl
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    dirty1 = atab.hyp_list
    dirty2 = atab.tar_list
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
        for j, i in enumerate(dirty1):
            pad1[j] = str(tlist1[i])
        for j, i in enumerate(dirty2):
            pad2[j] = str(tlist2[i])
        while tl.tlist1.line < len(dirty1):
            screen.pad1.cursor_down()
            screen.pad1.refresh()
            tl.tlist1.line += 1
        while tl.tlist2.line < len(dirty2):
            screen.pad2.cursor_down()
            screen.pad2.refresh()
            tl.tlist2.line += 1
        tl.tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
        tl.tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
        #screen.pad0.refresh()
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
    
def prevent_duplicates(screen, atab, nd1, nd2):
    tlist1 = atab.tl.tlist1.data
    nodes = nd1 + nd2

    def find(node, tree, line):
        for n in node.ancestors:
            old_tree = tlist1[n.line]
            if not is_implication(old_tree):
                if is_duplicate_upto_metavars(tree, old_tree):
                    if atab.tl.tlist1.dependency(line) == atab.tl.tlist1.dependency(n.line):
                        for dat in atab.hyp_nodes:
                            if dat.line == n.line:
                                return dat.applied
            applied = find(n, tree, line)
            if applied != None:
                return applied

        return None

    no_dup = False
    vacuous = True

    for node in nodes:
        tree = tlist1[node.line]
        if not is_implication(tree):
            vacuous = False
            applied = find(node, tree, node.line)
            if applied != None: # found duplicate
                for i in applied:
                    if i not in node.applied:
                        node.applied.append(i)
            else:
                no_dup = True

    return no_dup or vacuous

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

def load_theorem(screen, atab, temp_tl, filepos, line, defn=False):
    """
    Given a tableau and line where the theorem exists, copy the theorem into
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
            if defn:
                atab.tl.defn.append(len(tlist1) - 1)
        atab.libthms_loaded[filepos] = j # mark theorem as loaded
        for v in temp_tl.vars:
            atab.tl.vars[v] = temp_tl.vars[v] # update vars in main tableau (we can't replace vars struct due to var renaming)
        atab.tl.stree = temp_tl.stree # update sort graph in main tableau
            
    return dirty1, dirty2, line

def temp_load_theorem(screen, atab, filepos, line, defn=False):
    temp_tl = TreeList() # create a temporary tableau
    temp_tl.vars = deepcopy(atab.tl.vars) # copy variable subscript record from tl
    temp_tl.stree = atab.tl.stree # copy sort tree from tl
    sorts_mark(screen, atab.tl) # allow rollback of sort graph
    logic.library_import(screen, temp_tl, atab.library, filepos) # load the theorem into temporary tableau
    autocleanup(screen, temp_tl, TargetNode(-1, []), defn) # expand theorem into tableau with temporary target tree

    return temp_tl

def backwards_reasoning_possible(screen, atab, line2, filepos, line, pos, neg, rewrite, mv_check=True, defn=False):
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

        if tnode and line2 not in tnode.applied2: # check we haven't already applied this theorem to this head
            thm = tlist1[line] # theorem we are applying
            thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars

            if mv_check:
                mv1 = metavars_used(thm.left)
                mv2 = metavars_used(thm.right)
                pos = pos and set(mv1).issubset(mv2)
                neg = neg and set(mv2).issubset(mv1)
        
            if isinstance(thm, ImpliesNode): # reasoning
                thm, _ = relabel(screen, tl, univs, thm, True)
                if pos:
                    prec, u = unquantify(screen, thm.right, False)
                    if not isinstance(prec, AndNode):
                        # check if precedent unifies with hyp
                        unifies1, assign, macros = unify(screen, tl, prec, tlist2[line2]) # check modus ponens
                if not unifies1 and neg:
                    prec, u = unquantify(screen, thm.left, True)
                    if not isinstance(prec, AndNode):
                        # check if precedent unifies with hyp
                        unifies2, assign, macros = unify(screen, tl, complement_tree(prec), tlist2[line2]) # check modus tollens
            elif rewrite and isinstance(thm, EqNode): # rewriting
                unifies3, _, _ = logic.limited_equality_substitution(screen, atab.tl, atab.ttree, None, \
                                                                line, line2, False, True) # check rewriting
    else: # library theorem not yet loaded, load into temporary tableau
        temp_tl = temp_load_theorem(screen, atab, filepos, line, defn)

        thm = temp_tl.tlist1.data[line] # line of interest in theorem in temporary tableau
        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
        thm, _ = relabel(screen, temp_tl, univs, thm, True)

        if mv_check:
            mv1 = metavars_used(thm.left)
            mv2 = metavars_used(thm.right)
            pos = pos and set(mv1).issubset(mv2)
            neg = neg and set(mv2).issubset(mv1)

        if isinstance(thm, ImpliesNode): # reasoning
            if pos:
                prec, u = unquantify(screen, thm.right, False)
                # check theorem has only one precedent
                if not isinstance(prec, AndNode):
                    # check if precedent unifies with hyp
                    unifies1, assign, macros = unify(screen, temp_tl, prec, tlist2[line2]) # check modus ponens
            if neg and not unifies1:
                prec, u = unquantify(screen, thm.left, True)
                unifies2, assign, macros = unify(screen, temp_tl, complement_tree(prec), tlist2[line2]) # check modus tollens
        elif rewrite and isinstance(thm, EqNode): # rewriting
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
    
def forwards_reasoning_possible(screen, atab, imp, hyp, pos, neg, rewrite, mv_check=True, var_check=True, allow_ltor_violation=False):
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

def library_forwards_reasoning_possible(screen, atab, line2, filepos, line, pos, neg, rewrite, mv_check=True, var_check=True, defn=False):
    unifies1 = False
    unifies2 = False
    unifies3 = False

    tlist1 = atab.tl.tlist1.data
    tlist2 = atab.tl.tlist2.data
              
    if filepos in atab.libthms_loaded: # check if already loaded in tableau
        temp_tl = atab.tl
        line += atab.libthms_loaded[filepos]
    else:
        temp_tl = temp_load_theorem(screen, atab, filepos, line, defn)

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
        if not isinstance(prec, AndNode):
            # check if precedent unifies with hyp
            if var_check:
                v1 = vars_used(screen, atab.tl, prec)
                v2 = vars_used(screen, atab.tl, tlist1[line2])
            
            if not var_check or v1 or v2: # ensure not applying metavar thm to metavar head
                if pos and (not mv_check or mv_inc == 0):
                    unifies1, assign, macros = unify(screen, temp_tl, prec, tlist1[line2])
        if neg and not unifies1:
            prec, u = unquantify(screen, thm.right, False)
            if not isinstance(prec, AndNode) and (not mv_check or nmv_inc == 0):
                # check if precedent unifies with hyp
                if var_check:
                    v1 = vars_used(screen, atab.tl, prec)
                    v2 = vars_used(screen, atab.tl, tlist1[line2])
                        
                if not var_check or v1 or v2: # ensure not applying metavar thm to metavar head
                    unifies2, assign, macros = unify(screen, temp_tl, complement_tree(prec), tlist1[line2])
    elif rewrite and isinstance(thm, EqNode):
        temp_tlist1 = temp_tl.tlist1.data
        temp_tlist1.append(tlist1[line2])
        n = len(temp_tlist1) - 1
        unifies3, _, _ = logic.limited_equality_substitution(screen, temp_tl, atab.ttree, None, line, n, True, True)
        del temp_tlist1[n]

    if not unifies1 and not unifies2 and not unifies3:
        sorts_rollback(screen, atab.tl) # restore sort graph if temporary tableau was loaded

    return unifies1, unifies2, unifies3, temp_tl, line

def atomic_rewrite_possible(screen, atab, atomic, filepos, line):
    filtered_atomic = [] # implications that can be rewritten
    
    if filepos in atab.libthms_loaded: # check if already loaded in tableau
        temp_tl = atab.tl
        line += atab.libthms_loaded[filepos]
    else:
        temp_tl = temp_load_theorem(screen, atab, filepos, line, True)

    thm = temp_tl.tlist1.data[line] # line of interest in theorem in temporary tableau
    thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
    
    if isinstance(thm, ImpliesNode) and not isinstance(thm.right, ExistsNode) and \
                                                            not isinstance(thm.right, ForallNode):
        prec, u = unquantify(screen, thm.left, True)
        
        if not isinstance(prec, AndNode):
            for parent, n in atomic:
                tree = parent.left if n == 1 else parent.right

                if vars_used(screen, atab.tl, tree): # ensure not applying metavar thm to metavar head
                    unifies, assign, macros = unify(screen, temp_tl, prec, tree)
                 
                    if unifies:
                        filtered_atomic.append((parent, n))

    if not filtered_atomic:
        sorts_rollback(screen, atab.tl) # restore sort graph if temporary tableau was loaded

    return filtered_atomic, temp_tl, line

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
        success = False
        
        if unifies1: # modus ponens
           success, dirty1, dirty2 = logic.modus_ponens(screen, atab.tl, atab.ttree, dep, line1, [line2], is_hyp)
            
        if not success and unifies2: # modus tollens
            success, dirty1, dirty2 = logic.modus_tollens(screen, atab.tl, atab.ttree, dep, line1, [line2], is_hyp)
            
        if not success and unifies3: # rewriting
            success, dirty1, dirty2 = logic.limited_equality_substitution(screen, atab.tl, atab.ttree, dep, line1, line2, is_hyp, False)
    
        return success, dirty1, dirty2

def check_done(screen, atab, interface):
    dirty1, dirty2, done, plist = check_targets_proved(screen, atab.tl, atab.ttree, atab.start1, atab.start2, atab.hyp_list, atab.tar_list)

    atab.start1 = len(atab.tl.tlist1.data)
    atab.start2 = len(atab.tl.tlist2.data)

    if not done:
        tar_line = atab.hydra.tars[0]
                
        while isinstance(atab.tl.tlist2.data[tar_line], DeadNode): # check if current hydra proved
            if not atab.hydras:
                done = True
                break
            
            atab.hydra = atab.hydras.pop() # get new hydra
            tar_line = atab.hydra.tars[0]
            
    update_screen(screen, atab, interface, dirty1, dirty2)

    return done, plist

class HydraNode:
    def __init__(self, idx, tars):
        self.idx = idx # unique identifier for this hydra
        self.tars = tars # list of target indices in hydra

def get_initial_hydras(screen, atab):
    tar_idxs = [n.line for n in atab.tar_heads]
    hydras = find_hydras(atab.tl.tlist2.data, tar_idxs)
    atab.hydra_idx = 0
    for hlist in hydras:
        atab.hydras.append(HydraNode(atab.hydra_idx, hlist))
        atab.hydra_idx += 1    

def get_new_heads(screen, atab, n1):
    tlist1 = atab.tl.tlist1.data
    new_heads = []

    for idx in range(n1, len(tlist1)):
        if not is_implication(tlist1[idx]):
            node = get_autonode(screen, atab.hyp_heads, idx)
            if node: # check not dead
                new_heads.append(node) 

    return new_heads   

def hydra_append_new(screen, atab, tar, n2):
    tlist2 = atab.tl.tlist2.data

    tar_idxs = deepcopy(atab.hydra.tars)
    tar_idxs.remove(tar.line) # we've reasoned back from tar, remove it

    for i in range(n2, len(tlist2)): # add new lines
        if not isinstance(tlist2[i], DeadNode):
            tar_idxs.append(i)

    return tar_idxs

def hydra_split(screen, atab, line, tar_idxs):
    tlist2 = atab.tl.tlist2.data
    hydra = None

    # find hydra containing line
    for i in range(len(atab.hydras)):
        hydra = atab.hydras[i]
        found = False
        for tar_line in hydra.tars:
            if line == tar_line: # found the hydra
                found = True
                break
        if found:
            break        

    if hydra:
        atab.hydras.remove(hydra) # remove the hydra

    hydras = find_hydras(tlist2, tar_idxs)

    for hlist in hydras:
        hnode = HydraNode(atab.hydra_idx, hlist)

        atab.hydras.append(hnode)
        atab.hydra_idx += 1

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            hydra_split(screen, tab, line, tar_idxs)

def find_atomic_predicates(screen, tree):
    """
    Given a parse tree representing a predicate, find a list of pairs (p, n)
    where p is a node such that position n (1 = left or 2 = right) is an atomic
    predicate. If tree is itself an atomic predicate, [] is returned.
    """
    pred_list = []

    def find(tree):
        if tree == None:
            return False

        if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            find(tree.left)
            return False

        if not isinstance(tree, NotNode) and not isinstance(tree, ImpliesNode) and \
           not isinstance(tree, AndNode) and not isinstance(tree, OrNode):
            return True

        if find(tree.left):
            pred_list.append((tree, 1))

        if find(tree.right):
            pred_list.append((tree, 2))

        return False

    find(tree)
    return pred_list

def apply_atomic_rewrite(screen, atab, dirty1, dirty2, parent, n, len1, line1, line2):
    """
    Given the right implication of an iff statement on line1 of the tableau, rewrite
    the expression parent.left if n == 1 or parent.right if n == 2, parent being the
    parent of the atomic predicate being rewritten, which is part of line2 in the
    tableau. The resulting expression will be placed on line len1 of the tableau.
    """
    tlist1 = atab.tl.tlist1.data
    
    subst = tlist1[line1]
    subst, univs = unquantify(screen, subst, True)
    prec = subst.left

    tree = deepcopy(parent.left) if n == 1 else deepcopy(parent.right) # make copy of tree being replaced
    dep = atab.tl.tlist1.dependency(line2)
     
    unifies, assign, macros = unify(screen, atab.tl, prec, tree)
    rewrite = substitute(subst.right, assign) # compute the rewritten expression

    # replace atomic predicate by rewrite
    if n == 1:
        parent.left = rewrite 
    else:
        parent.right = rewrite

    if len1 == len(tlist1): # we are appending
        append_tree(tlist1, deepcopy(tlist1[line2]), dirty1)
        atab.tl.tlist1.dep[len1] = dep
        record_move(screen, atab.tl, len1, ('e', line1, [line2]))
    else:
        replace_tree(tlist1, len1, deepcopy(tlist1[line2]), dirty1)

def mark_hyp_active(atab, hyp):
    if hyp not in atab.hyps_active:
        atab.hyps_active.append(hyp)

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            mark_hyp_active(tab, hyp)
        
def mark_hyp_inactive(atab, hyp):
    if hyp in atab.hyps_active:
        atab.hyps_active.remove(hyp)

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            mark_hyp_inactive(tab, hyp)
        
def mark_tar_inactive(atab, tar):
    if tar in atab.tars_active:
        atab.tars_active.remove(tar)

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            mark_tar_inactive(tab, tar)

def get_tab_dep(tab1, tab2):
    def find(tab1, tab2):
        if tab1 == tab2:
            return tab1

        tab1.marked = True

        for tab in tab1.descendants:
            if not tab.marked:
                found = find(tab, tab2)
                if found:
                    return found
        return None

    found = find(tab1, tab2)
    unmark(tab1)
    if not found:
        found = find(tab2, tab1)
        unmark(tab2)
        if not found:
            tabs = list(set(tab1.descendants).intersection(tab2.descendants))
            if len(tabs) == 1:
                found = tabs[0]
            else:
                raise Exception("Invalid hypothesis dependency information")

    return found
        
def copy_tableau(atab, copy_descendants=False):
    global tab_count

    new_tab = copy(atab)
    new_tab.ttree = deepcopy(atab.ttree) # ttree is maintained per tableau
    new_tab.hydras = deepcopy(atab.hydras) # hydras are maintained per tableau
    new_tab.tl = copy(atab.tl) # tl maintained per tableau
    new_tab.tl.tlist1 = copy(atab.tl.tlist1)
    new_tab.tl.tlist2 = copy(atab.tl.tlist2)
    new_tab.tl.tlist1.data = copy(atab.tl.tlist1.data) # tlist1 maintained per tableau
    new_tab.tl.tlist2.data = copy(atab.tl.tlist2.data) # tlist2 maintained per tableau
    new_tab.hyps_active = copy(atab.hyps_active) # hypotheses active maintained per tableau
    new_tab.tars_active = copy(atab.tars_active) # hypotheses active maintained per tableau
    if copy_descendants:
        new_tab.descendants = copy(atab.descendants)
    else:
        new_tab.descendants = [] # descendants of this tableau (tree of tableaus)
    new_tab.hyp_list = copy(atab.hyp_list) # hyp_list maintained per tableau
    new_tab.tar_list = copy(atab.tar_list) # tar_list maintained per tableau
    new_tab.tar_heads = copy(atab.tar_heads) # tar_heads maintained per tableau
    new_tab.hyp_heads = copy(atab.hyp_heads) # hyp_heads maintained per tableau
    new_tab.hyp_impls = copy(atab.hyp_impls) # hyp_impls maintained per tableau
    new_tab.tl.hyp_tab = copy(atab.tl.hyp_tab) # hyp_tab maintained per tableau
    new_tab.tl.tar_tab = copy(atab.tl.tar_tab) # tar_tab maintained per tableau
    new_tab.num = tab_count
    tab_count += 1

    return new_tab

def display_tabs(screen, atab):
    def disp(atab):
        if atab.descendants:
            screen.dialog(str(atab.num)+"->"+str([t.num for t in atab.descendants]))
        atab.marked = True
        for tab in atab.descendants:
            if not tab.marked:
                disp(tab)

    disp(atab)
    unmark(atab)

def check_lengths(atab, length=0):
    n = len(atab.tl.tlist1.data)    

    if length != 0 and length != n:
        raise Exception("Not right length")
    
    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            check_lengths(tab, n)

def add_ancestors(nd1, nd2, head, impl):
    for node in nd1:
        if head not in node.ancestors:
            node.ancestors.append(head)
        if impl != None and impl not in node.ancestors:
            node.ancestors.append(impl)

    for node in nd2:
        if head not in node.ancestors:
            node.ancestors.append(head)
        if impl != None and impl not in node.ancestors:
            node.ancestors.append(impl)

def update_split_line(screen, atab, line, tree):
    atab.tl.tlist1.data[line] = tree

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            update_split_line(screen, tab, line, tree)

def duplicate_tableau_trees(screen, atab, tab_dict):
    tab_list = atab.descendants

    for i, tab in enumerate(tab_list):
        if tab in tab_dict:
            tab_list[i] = tab_dict[tab]
        else:
            tab_list[i] = copy_tableau(tab, True)
            tab_dict[tab] = tab_list[i]  

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            duplicate_tableau_trees(screen, tab, tab_dict)

def rewrite_hyp_tar_tabs(screen, atab, tab_dict):
    hyp_tab = atab.tl.hyp_tab
    tar_tab = atab.tl.tar_tab
    
    for i in range(len(hyp_tab)):
        if hyp_tab[i] in tab_dict:
            hyp_tab[i] = tab_dict[hyp_tab[i]]

    for i in range(len(tar_tab)):
        if tar_tab[i] in tab_dict:
            tar_tab[i] = tab_dict[tar_tab[i]]

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            rewrite_hyp_tar_tabs(screen, tab, tab_dict)

def find_tab(atab, tab, level=0):
    if tab == atab:
        return atab, level
    
    for t in atab.descendants:
        a, l = find_tab(t, tab, level + 1)
        if a:
            return a, l
    
    return None, None

def remove_tab(atab, tab, level=0):
    if tab == atab:
        return atab, level
    
    for t in atab.descendants:
        a, l = remove_tab(t, tab, level + 1)
        if a:
            if l == level + 1:
                atab.descendants.remove(tab)
            return a, l
    
    return None, None

def reinsert_head(screen, atab, head):
    if head in atab.hyp_heads:
        atab.hyp_heads.remove(head)
    insert_sort(screen, atab.hyp_heads, head)
    if head not in atab.hyps_active:
        atab.hyps_active.append(head)
    atab.start1 = min(atab.start1, head.line)

    atab.marked = True

    for tab in atab.descendants:
        if not tab.marked:
            reinsert_head(screen, tab, head)

def automate(screen, tl, ttree, interface='curses'):
    global automation_limit

    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data

    library = open("library.dat", "r")
    index, constants, constant_order = create_index(screen, tl, library)

    atab = AutoTab(screen, tl, ttree, library, constants, constant_order) # initialise automation data structure
    atab.top_tab = atab

    # mark everything as active
    for node in atab.hyp_heads:
         if node not in atab.hyps_active:
            atab.hyps_active.append(node)

    for node in atab.hyp_impls:
         if node not in atab.hyps_active:
            atab.hyps_active.append(node)

    for node in atab.tar_heads:
        if node not in atab.tars_active:
            atab.tars_active.append(node)

    # annotate initial hypothesis tableau dependencies
    for i in range(len(tl.tlist1.data)):
        atab.tl.hyp_tab.append(atab)

    for i in range(len(tl.tlist2.data)):
        atab.tl.tar_tab.append(atab)

    atab_list = [atab] # initial list of tableaus
        
    # make initial list of hydra nodes
    get_initial_hydras(screen, atab)

    done = False
        
    while atab_list:
        old_atab = atab
        atab = atab_list.pop() # get new tableau
        if done:
            remove_tab(atab.top_tab, old_atab)

        remove_tabs = [] # tableaus identical to the current one
        for tab2 in atab_list:
            if all(node in tab2.hyps_active for node in atab.hyps_active) and \
               all(node in tab2.tars_active for node in atab.tars_active) and \
               all(node in atab.hyps_active for node in tab2.hyps_active) and \
               all(node in atab.tars_active for node in tab2.tars_active):
                  remove_tabs.append(tab2)
        for tab2 in remove_tabs:
            atab_list.remove(tab2)
                
        screen.debug("New tableau: "+str(atab.num))

        tlist1 = atab.tl.tlist1.data
        tlist2 = atab.tl.tlist2.data

        atab.hydra = atab.hydras.pop() # get a hydra
            
        done, _ = check_done(screen, atab, interface)
        old_bt_list = [] # used by backtracking

        if autotab_remove_deadnodes(screen, atab, [], [], interface):
            library.close()
            automation_limit += automation_increment
            return False, atab.tl

        if done:
            continue

        clear_screen(screen, atab.tl, interface)
        update_screen(screen, atab, interface)

        done = False # whether all targets are proved
        
        while True: # keep going until theorem proved or progress stalls
            progress = False # whether progress was made at some level of the waterfall

            # get all constants in active hypotheses
            hypc = []
            
            for v in atab.hyp_heads:
                if v in atab.hyps_active:
                    hypc = list_merge(hypc, v.const1)
                    hypc = list_merge(hypc, v.nconst1)

            for v in atab.hyp_impls:
                if v in atab.hyps_active:
                    c = list_merge(v.const1, v.const2)
                    hypc = list_merge(hypc, c)
                    c = list_merge(v.nconst1, v.nconst2)
                    hypc = list_merge(hypc, c)

            # get all constants in active entries in tableau
            tabc = deepcopy(hypc)

            for v in atab.tar_heads:
                if v in atab.tars_active:
                    tabc = list_merge(tabc, v.const1)
                    tabc = list_merge(tabc, v.nconst1)

            # 1) See if there are any theorems/defns to load which are not implications

            libthms = filter_theorems3(screen, index, tabc)
            for (title, filepos, line) in libthms:

                # check to see if thm already loaded, if not, load it
                if filepos not in atab.libthms_loaded:
                    progress = True # we made progress affecting tableau

                    logic.library_import(screen, atab.tl, library, filepos)

                    n1 = len(tlist1) # any lines after this have been added
                    n2 = len(tlist2)      

                    j = len(tlist1) - 1
                    nd1, _ = update_autotab(screen, atab, atab.top_tab, [j], [], interface, 0, special=True)
                    atab.libthms_loaded[filepos] = j

                    dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                    nd2, _ = update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, 0, special=True)
                    # update_screen(screen, atab.tl, interface, dirty1, dirty2)

                    done, partial = check_done(screen, atab, interface)
                    if partial:
                        old_bt_list = [] # reset backtracking 

                    if autotab_remove_deadnodes(screen, atab, [], [], interface):
                        library.close()
                        automation_limit += automation_increment
                        return False, atab.tl

                    check_lengths(atab.top_tab)
                    unmark(atab.top_tab)

                    screen.debug("New non-implication thm loaded")

                    if done:
                        break

            if done:
                break

            if progress:
                continue    

            # Everything from here focuses on the current hydra

            # 2) Non-library backwards reasoning

            for tar_line in atab.hydra.tars:
                tar = get_autonode(screen, atab.tar_heads, tar_line)
                # get all active implications dependency compatible with target 
                impls = []

                for v in atab.hyp_impls:
                    if v in atab.hyps_active and deps_compatible(screen, atab.tl, atab.ttree, tar.line, v.line):
                        insert_sort(screen, impls, v)

                line2 = tar.line

                for impl, pos, neg in filter_implications1(screen, atab, impls, tar.const1):
                    line1 = impl.line    

                    if line2 not in impl.applied2: # check we didn't already apply this impl to this target
                        impl.applied2.append(line2) # mark impl as applied to our target
                            
                        n1 = len(tlist1) # any lines added after these are new
                        n2 = len(tlist2)

                        success, dirty1, dirty2 = apply_theorem(screen, atab, pos, neg, False, line1, line2, False)
                        if success:
                            hyp_tab_dep = atab.tl.hyp_tab[line1]
                            tar_tab_dep = atab.tl.tar_tab[line2]
                            tab_dep = get_tab_dep(hyp_tab_dep, tar_tab_dep)

                            mark_tar_inactive(tab_dep, tar)
                            unmark(tab_dep)

                            update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                            dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                            update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                            
                            if True: # c1 and c2:
                                tree = atab.tl.tlist1.data[line1]
                                if isinstance(tree, ImpliesNode):
                                    mv1 = metavars_used(tree.left)
                                    mv2 = metavars_used(tree.right)
                                    if len(set(mv1).intersection(mv2)) == 0: # no shared metavars
                                        mark_hyp_inactive(tab_dep, impl)

                            
                                tar_idxs = hydra_append_new(screen, atab, tar, n2) # split the current hydra and reinsert
                                atab.hydras.append(atab.hydra)
                                hydra_split(screen, tab_dep, tar.line, tar_idxs)
                                unmark(tab_dep)

                                if atab.hydras:
                                    atab.hydra = atab.hydras.pop() # get new hydra

                                progress = True

                                done, partial = check_done(screen, atab, interface)
                                if partial:
                                    old_bt_list = [] # reset backtracking 

                                screen.debug("Backwards non-library reasoning")

                            if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                library.close()
                                automation_limit += automation_increment
                                return False, atab.tl

                            check_lengths(atab.top_tab)
                            unmark(atab.top_tab)
                    
                            if done or progress:
                                break

                if done or progress:
                    break

            if done:
                break

            if progress:
                continue

            # 3) Non-library forwards reasoning

            # get all active implications and heads dependency compatible with current hydra
            impls = []
            heads = []
                
            for tar_line in atab.hydra.tars:
                tar = get_autonode(screen, atab.tar_heads, tar_line)
                for v in atab.hyp_impls:
                    if v in atab.hyps_active and deps_compatible(screen, atab.tl, atab.ttree, tar.line, v.line):
                        if v not in impls:
                            insert_sort(screen, impls, v)

                for v in atab.hyp_heads:
                    if (v in atab.hyps_active or v.special) and deps_compatible(screen, atab.tl, atab.ttree, tar.line, v.line):
                        if v not in heads:
                            insert_sort(screen, heads, v)

            for head in heads:
                line2 = head.line

                for impl, pos, neg in filter_implications2(screen, atab, impls, head.const1, special=head.special):
                    line1 = impl.line    

                    if line1 not in head.applied: # check we didn't already apply this impl to this head
                        head.applied.append(line1) # mark head as applied with our impl

                        n1 = len(tlist1) # any lines added after these are new
                        
                        success, dirty1, dirty2 = apply_theorem(screen, atab, pos, neg, False, line1, line2, True)

                        if success:
                            head.backtrackable = True
                            depth = max(head.depth, impl.depth) + 1

                            hyp_tab_dep1 = atab.tl.hyp_tab[line1]
                            hyp_tab_dep2 = atab.tl.hyp_tab[line2]
                            tab_dep = get_tab_dep(hyp_tab_dep1, hyp_tab_dep2)

                            nd1, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                            for node in nd1:
                                node.applied.append(line1)
                            dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                            nd2, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                            for node in nd2:
                                if line1 not in node.applied:
                                    node.applied.append(line1)
                            add_ancestors(nd2, nd1, head, impl)
                            c1 = prevent_duplicates(screen, atab, nd1, nd2)

                            if c1:
                                tree = atab.tl.tlist1.data[line1]
                                if isinstance(tree, ImpliesNode):
                                    mv1 = metavars_used(tree.left)
                                    mv2 = metavars_used(tree.right)
                                    if len(set(mv1).intersection(mv2)) == 0: # no shared metavars
                                        mark_hyp_inactive(tab_dep, impl)

                                if not head.type:
                                    mark_hyp_inactive(tab_dep, head)
                                    unmark(tab_dep)

                                progress = True

                                done, partial = check_done(screen, atab, interface)
                                if partial:
                                    old_bt_list = [] # reset backtracking 
                                
                                screen.debug("Forwards non-library reasoning")

                            if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                library.close()
                                automation_limit += automation_increment
                                return False, atab.tl

                            check_lengths(atab.top_tab)
                            unmark(atab.top_tab)
                    
                            if done or progress:
                                break

                if done or progress:
                    break

            if done:
                break

            if progress:
                continue

            # 4) See if there are any disjunctions as hypotheses where we can split the tableau
            for impl in impls:
                line = impl.line
                tree = tlist1[line]
                if isinstance(tree, ImpliesNode):
                    mv1 = metavars_used(tree.left)
                    mv2 = metavars_used(tree.right)
                    if len(set(mv1).intersection(mv2)) == 0: # there are no shared metavars
                        atab.hydras.append(atab.hydra) # reinsert current hydra
                        atab.hydra = None

                        old_node = get_autonode(screen, atab.hyp_nodes, line) # get node for old line
                        parent = atab.tl.hyp_tab[line] # parent of this line

                        # P \implies Q will be replaced by ¬P and P \wedge Q
                        alt_tree1 = deepcopy(complement_tree(tree.left))
                        new_tab1 = copy_tableau(parent)
                        new_tab1.tl.tlist1.data[line] = alt_tree1 # insert ¬P

                        alt_tree2 = AndNode(deepcopy(tree.left), deepcopy(tree.right))
                        new_tab2 = copy_tableau(parent)
                        new_tab2.tl.tlist1.data[line] = alt_tree2 # insert P \wedge Q

                        if parent == atab: # ordinary split from current tableau
                            atab.descendants = [new_tab1, new_tab2]

                            atab_list.append(new_tab2)
                            atab_list.append(new_tab1)

                        else: # part of the tree needs duplication
                            atab_list.append(atab) # reinsert current tableau in atab_list
                            new_atab_list = [] # update atab_list
                          
                            for tab in parent.descendants:
                                tab2 = copy_tableau(tab, True) # copy descendants of parents
                                tab3 = copy_tableau(tab, True) # copy descendants of parents
                                tab.descendants = [tab2, tab3] # link up pseudo-tableaus to originals
                                new_tab1.descendants.append(tab2) # also link to new_tab1
                                new_tab2.descendants.append(tab3) # also link to new_tab1
                                if tab in atab_list:
                                    new_atab_list.append(tab2)
                                    new_atab_list.append(tab3)
                                    atab_list.remove(tab)
                            
                            tab_dict = dict() # dictionary matching old tabs to copies

                            for tab in new_tab2.descendants:
                                duplicate_tableau_trees(screen, tab, tab_dict)
                            
                            for tab in new_tab2.descendants:
                                unmark(tab)
                            
                            rewrite_hyp_tar_tabs(screen, new_tab2, tab_dict)
                            unmark(new_tab2)
                            update_split_line(screen, new_tab1, line, alt_tree1)
                            unmark(new_tab1)
                            update_split_line(screen, new_tab2, line, alt_tree2)
                            unmark(new_tab2)
                            
                            parent.descendants.append(new_tab1)
                            parent.descendants.append(new_tab2)

                            for tab in atab_list:
                                new_atab_list.append(tab)
                                if tab in tab_dict:
                                    new_atab_list.append(tab_dict[tab])

                            while atab_list:
                                atab_list.pop()
                                
                            for tab in new_atab_list:
                                atab_list.append(tab)
                            
                        # create new autotab for the new line
                        nd1, _ = update_autotab(screen, new_tab1, new_tab1, [line], [], interface, old_node.depth, split_line=line)
            
                        node = nd1[0]
                        node.ancestors = copy(old_node.ancestors) # add derivation history to node
                    
                        # apply cleanup moves to new line
                        dirty1, dirty2 = autocleanup(screen, new_tab1.tl, new_tab1.ttree)
                        nd2, _ = update_autotab(screen, new_tab1, new_tab1, dirty1, dirty2, interface, old_node.depth + 1, split_line=line)

                        for node2 in nd2:
                            if node2 != node:
                                node2.ancestors = copy(old_node.ancestors) # add derivation history to any new nodes

                        new_tab1.start1 = min(new_tab1.start1, line) # reset incremental completion checking to new line

                        # create new autotab for the new line
                        nd1, _ = update_autotab(screen, new_tab2, new_tab2, [line], [], interface, old_node.depth, split_line=line)
            
                        node = nd1[0]
                        node.ancestors = copy(old_node.ancestors) # add derivation history to node
                    
                        # apply cleanup moves to new line
                        dirty1, dirty2 = autocleanup(screen, new_tab2.tl, new_tab2.ttree)
                        nd2, _ = update_autotab(screen, new_tab2, new_tab2, dirty1, dirty2, interface, old_node.depth + 1, split_line=line)

                        for node2 in nd2:
                            if node2 != node:
                                node2.ancestors = copy(old_node.ancestors) # add derivation history to any new nodes

                        new_tab2.start1 = min(new_tab2.start1, line) # reset incremental completion checking to new line
                                    
                        progress = True

                        check_lengths(atab.top_tab)
                        unmark(atab.top_tab)
                    
                        screen.debug("Tableau split")

                        break

            if progress:
                break

            ht = get_constants_qz(screen, atab.tl, atab.tl.tlist0.data[0]) if atab.tl.tlist0.data else [] # type constants

            # 5) Type judgement

            for head in heads:
                line2 = head.line

                libthms = filter_judgements1(screen, index, ht, head.const1, tabc)

                for (title, pos, neg, filepos, line) in libthms:
                    if filepos < head.filepos_done or (filepos == head.filepos_done and line < head.line_done):
                        continue

                    head.filepos_done = filepos
                    head.line_done = line + 1
                    
                    unifies1, unifies2, unifies3, temp_tl, line = library_forwards_reasoning_possible(screen, \
                                                                atab, line2, filepos, line, pos, neg, False)

                    if unifies1 or unifies2:
                        # transfer library result to tableau
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line)
                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, head.depth + 1, False, library=True)

                        thmnode = get_autonode(screen, atab.hyp_impls, line1) # get autonode for theorem we want to apply
                        if (pos and thmnode.ltor) or (neg and thmnode.rtol):
                            tree = tlist1[line2]
                            if isinstance(tree, ElemNode) and isinstance(tree.left, VarNode):
                                varname = tree.left.name()
                                applied = False
                                for var, tline in thmnode.type_applied:
                                    if var == varname:
                                        for hyp in atab.hyps_active:
                                            if hyp.line == tline:
                                                deps1 = atab.tl.tlist1.dependency(line2)
                                                deps2 = atab.tl.tlist1.dependency(tline)
                                                if -1 in deps2 or all(dep in deps2 for dep in deps1):
                                                    applied = True
                                                    break
                                    if applied:
                                        break
                                if not applied and line1 not in head.applied: # check we didn't already apply this impl to this head
                                    n1 = len(tlist1) # any lines added after these are new
                                    
                                    success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, False, line1, line2, True)

                                    if success:
                                        head.backtrackable = True
                                        depth = head.depth + 1

                                        hyp_tab_dep1 = atab.tl.hyp_tab[line1]
                                        hyp_tab_dep2 = atab.tl.hyp_tab[line2]
                                        tab_dep = get_tab_dep(hyp_tab_dep1, hyp_tab_dep2)
                                        
                                        nd1, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                        for node in nd1:
                                            node.applied.append(line1)
                                            node.type = True
                                            newline = node.line
                                        dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                        nd2, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                        for node in nd2:
                                            if line1 not in node.applied:
                                                node.applied.append(line1)
                                            newline = node.line
                                            node.type = True
                                        add_ancestors(nd2, nd1, head, None)
                                        head.applied.append(line1) # mark head as applied with our impl
                                        thmnode.type_applied.append((varname, newline))
            
                                        c1 = prevent_duplicates(screen, atab, nd1, nd2)

                                        if c1:
                                            progress = True

                                            done, partial = check_done(screen, atab, interface)
                                            if partial:
                                                old_bt_list = [] # reset backtracking 
                                            
                                            screen.debug("Type judgement")

                                        if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                            library.close()
                                            automation_limit += automation_increment
                                            return False, atab.tl

                                        check_lengths(atab.top_tab)
                                        unmark(atab.top_tab)
                        
                                        if done or progress:
                                            break

                if done or progress:
                    break

            if done:
                break

            if progress:
                continue

            # 6) Safe target expansion
            for tar in atab.hydra.tars:
                tar = get_autonode(screen, atab.tar_heads, tar_line)
                libthms = filter_definitions2(screen, atab, index, tar.const1, hypc, library=False)
                
                for (title, pos, neg, rewrite, filepos, line) in libthms:
                    # check to see if thm already loaded
                    line2 = tar.line
                    
                    unifies1, unifies2, unifies3, temp_tl, line = backwards_reasoning_possible(screen, \
                                            atab, line2, filepos, line, pos, neg, rewrite, mv_check=True, defn=True)
                    
                    if unifies1 or unifies2 or unifies3:
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line, defn=True)

                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, 0, True, library=True) # update autotab with new lines

                        thmnode = get_autonode(screen, atab.hyp_impls, line1) # get autonode for theorem we want to apply
                        
                        if tar.line not in thmnode.applied2: # check we haven't applied it before
                            thmnode.applied2.append(tar.line) # mark theorem as applied to our target
                            
                            n1 = len(tlist1) # any lines added after these are new
                            n2 = len(tlist2)

                            success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, False)
                            
                            if success:
                                hyp_tab_dep = atab.tl.hyp_tab[line1]
                                tar_tab_dep = atab.tl.tar_tab[line2]
                                tab_dep = get_tab_dep(hyp_tab_dep, tar_tab_dep)
                                
                                update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                                dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                        
                                if True: # c1 and c2:
                                    tar_idxs = hydra_append_new(screen, atab, tar, n2) # split the current hydra and reinsert
                                    atab.hydras.append(atab.hydra)
                                    hydra_split(screen, tab_dep, tar.line, tar_idxs)
                                    unmark(tab_dep)
                            
                                    if atab.hydras:
                                        atab.hydra = atab.hydras.pop() # get new hydra

                                    progress = True

                                    done, partial = check_done(screen, atab, interface)
                                    if partial:
                                        old_bt_list = [] # reset backtracking 
                                    
                                    screen.debug("Safe target expansion")

                                if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False, atab.tl

                                check_lengths(atab.top_tab)
                                unmark(atab.top_tab)
                    
                                if done or progress:
                                    break
                if done or progress:
                    break
            
            if done:
                break

            if progress:
                continue

            # 7) Safe hypothesis expansion

            for head in heads:
                line2 = head.line

                libthms = filter_definitions1(screen, atab, index, ht, head.const1, tabc, library=False)
                
                for (title, pos, neg, rewrite, filepos, line) in libthms:
                    unifies1, unifies2, unifies3, temp_tl, line = library_forwards_reasoning_possible(screen, \
                                                atab, line2, filepos, line, pos, neg, rewrite, mv_check=True, defn=True)

                    if unifies1 or unifies2 or unifies3:
                        # transfer library result to tableau
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line, defn=True)
                        
                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, head.depth + 1, True, library=True)

                        if line1 not in head.applied: # check we didn't already apply this impl to this head
                            head.applied.append(line1) # mark head as applied with our impl

                            n1 = len(tlist1) # any lines added after these are new
                            
                            success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, True)

                            if success:
                                head.backtrackable = True
                                depth = head.depth + 1

                                hyp_tab_dep1 = atab.tl.hyp_tab[line1]
                                hyp_tab_dep2 = atab.tl.hyp_tab[line2]
                                tab_dep = get_tab_dep(hyp_tab_dep1, hyp_tab_dep2)

                                nd1, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                
                                nd2, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                add_ancestors(nd2, nd1, head, None)
                                c1 = prevent_duplicates(screen, atab, nd1, nd2)

                                if c1:
                                    if not head.type:
                                        mark_hyp_inactive(tab_dep, head)
                                        unmark(tab_dep)

                                    progress = True
                                    
                                    done, partial = check_done(screen, atab, interface)
                                    if partial:
                                        old_bt_list = [] # reset backtracking 
                                    
                                if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False, atab.tl

                                check_lengths(atab.top_tab)
                                unmark(atab.top_tab)
                    
                                if done or progress:
                                    break

                if done or progress:
                    break

            if done:
                break

            if progress:
                continue

            # 8) Target expansion
            for tar in atab.hydra.tars:
                tar = get_autonode(screen, atab.tar_heads, tar_line)
                libthms = filter_definitions2(screen, atab, index, tar.const1, hypc, library=True)
                
                for (title, pos, neg, rewrite, filepos, line) in libthms:
                    # check to see if thm already loaded
                    line2 = tar.line
                    
                    unifies1, unifies2, unifies3, temp_tl, line = backwards_reasoning_possible(screen, \
                                            atab, line2, filepos, line, pos, neg, rewrite, mv_check=False, defn=True)
                    
                    if unifies1 or unifies2 or unifies3:
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line, defn=True)

                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, 0, True, library=True) # update autotab with new lines

                        thmnode = get_autonode(screen, atab.hyp_impls, line1) # get autonode for theorem we want to apply
                        
                        if tar.line not in thmnode.applied2: # check we haven't applied it before
                            thmnode.applied2.append(tar.line) # mark theorem as applied to our target
                            
                            n1 = len(tlist1) # any lines added after these are new
                            n2 = len(tlist2)

                            success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, False)
                            
                            if success:
                                hyp_tab_dep = atab.tl.hyp_tab[line1]
                                tar_tab_dep = atab.tl.tar_tab[line2]
                                tab_dep = get_tab_dep(hyp_tab_dep, tar_tab_dep)
                                
                                update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                                dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                        
                                if True: # c1 and c2:
                                    tar_idxs = hydra_append_new(screen, atab, tar, n2) # split the current hydra and reinsert
                                    atab.hydras.append(atab.hydra)
                                    hydra_split(screen, tab_dep, tar.line, tar_idxs)
                                    unmark(tab_dep)

                                    if atab.hydras:
                                        atab.hydra = atab.hydras.pop() # get new hydra

                                    progress = True

                                    done, partial = check_done(screen, atab, interface)
                                    if partial:
                                        old_bt_list = [] # reset backtracking 
                                    
                                    screen.debug("Target expansion")

                                if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False, atab.tl

                                check_lengths(atab.top_tab)
                                unmark(atab.top_tab)
                    
                                if done or progress:
                                    break
                if done or progress:
                    break
            
            if done:
                break

            if progress:
                continue

            # 9) Forwards library reasoning

            for head in heads:
                line2 = head.line

                libthms = filter_theorems1(screen, index, ht, head.const1, tabc)

                for (title, pos, neg, filepos, line) in libthms:
                    if filepos < head.filepos_done or (filepos == head.filepos_done and line < head.line_done):
                        continue

                    head.filepos_done = filepos
                    head.line_done = line + 1
                    
                    unifies1, unifies2, unifies3, temp_tl, line = library_forwards_reasoning_possible(screen, \
                                                                atab, line2, filepos, line, pos, neg, False)

                    if unifies1 or unifies2:
                        # transfer library result to tableau
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line)
                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, head.depth + 1, False, library=True)

                        thmnode = get_autonode(screen, atab.hyp_impls, line1) # get autonode for theorem we want to apply
                        if (pos and thmnode.ltor) or (neg and thmnode.rtol):
                            if line1 not in head.applied: # check we didn't already apply this impl to this head
                                head.applied.append(line1) # mark head as applied with our impl

                                n1 = len(tlist1) # any lines added after these are new
                                
                                success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, False, line1, line2, True)

                                if success:
                                    head.backtrackable = True
                                    depth = head.depth + 1

                                    hyp_tab_dep1 = atab.tl.hyp_tab[line1]
                                    hyp_tab_dep2 = atab.tl.hyp_tab[line2]
                                    tab_dep = get_tab_dep(hyp_tab_dep1, hyp_tab_dep2)
                                    
                                    nd1, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                    for node in nd1:
                                        node.applied.append(line1)
                                    dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                    nd2, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                    for node in nd2:
                                        if line1 not in node.applied:
                                            node.applied.append(line1)
                                    add_ancestors(nd2, nd1, head, None)
                                    c1 = prevent_duplicates(screen, atab, nd1, nd2)

                                    if c1:
                                        if not head.type:
                                            mark_hyp_inactive(tab_dep, head)
                                            unmark(tab_dep)

                                        progress = True

                                        done, partial = check_done(screen, atab, interface)
                                        if partial:
                                            old_bt_list = [] # reset backtracking 
                                        
                                        screen.debug("Forwards library reasoning")

                                    if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                        library.close()
                                        automation_limit += automation_increment
                                        return False, atab.tl

                                    check_lengths(atab.top_tab)
                                    unmark(atab.top_tab)
                    
                                    if done or progress:
                                        break

                if done or progress:
                    break

            if done:
                break

            if progress:
                continue

            # 10) Backwards library reasoning

            for tar_line in atab.hydra.tars:
                tar = get_autonode(screen, atab.tar_heads, tar_line)
                libthms = filter_theorems2(screen, atab, index, tar.const1, hypc)

                for (title, pos, neg, filepos, line) in libthms:
                    # check to see if thm already loaded
                    line2 = tar.line
                    
                    unifies1, unifies2, unifies3, temp_tl, line = backwards_reasoning_possible(screen, \
                                                                            atab, line2, filepos, line, pos, neg, False)

                    if unifies1 or unifies2:
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line)

                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, 0, False, library=True) # update autotab with new lines

                        thmnode = get_autonode(screen, atab.hyp_impls, line1) # get autonode for theorem we want to apply
                        if (pos and not thmnode.ltor) or (neg and not thmnode.rtol):
                            if tar.line not in thmnode.applied2: # check we haven't applied it before
                                thmnode.applied2.append(tar.line) # mark theorem as applied to our target
                                
                                n1 = len(tlist1) # any lines added after these are new
                                n2 = len(tlist2)

                                success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, False)

                                if success:
                                    hyp_tab_dep = atab.tl.hyp_tab[line1]
                                    tar_tab_dep = atab.tl.tar_tab[line2]
                                    tab_dep = get_tab_dep(hyp_tab_dep, tar_tab_dep)

                                    update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                                    dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                    update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, 0, False)
                            
                                    if True: # c1 and c2:
                                        tar_idxs = hydra_append_new(screen, atab, tar, n2) # split the current hydra and reinsert
                                        atab.hydras.append(atab.hydra)
                                        hydra_split(screen, tab_dep, tar.line, tar_idxs)
                                        unmark(tab_dep)

                                        if atab.hydras:
                                            atab.hydra = atab.hydras.pop() # get new hydra

                                        progress = True

                                        done, partial = check_done(screen, atab, interface)
                                        if partial:
                                            old_bt_list = [] # reset backtracking 
                                        
                                        screen.debug("Backwards library reasoning")

                                    if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                        library.close()
                                        automation_limit += automation_increment
                                        return False, atab.tl

                                    check_lengths(atab.top_tab)
                                    unmark(atab.top_tab)
                    
                                    if done or progress:
                                        break
                if done or progress:
                    break

            if done:
                break

            if progress:
                continue
                
            # 11) Hypothesis expansion

            for head in heads:
                line2 = head.line

                libthms = filter_definitions1(screen, atab, index, ht, head.const1, tabc, library=True)
                
                for (title, pos, neg, rewrite, filepos, line) in libthms:
                    
                    unifies1, unifies2, unifies3, temp_tl, line = library_forwards_reasoning_possible(screen, \
                                                atab, line2, filepos, line, pos, neg, rewrite, mv_check=False, defn=True)

                    if unifies1 or unifies2 or unifies3:
                        # transfer library result to tableau
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line, defn=True)
                        
                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, head.depth + 1, True, library=True)

                        if line1 not in head.applied: # check we didn't already apply this impl to this head
                            head.applied.append(line1) # mark head as applied with our impl

                            n1 = len(tlist1) # any lines added after these are new
                            
                            success, dirty1, dirty2 = apply_theorem(screen, atab, unifies1, unifies2, unifies3, line1, line2, True)

                            if success:
                                head.backtrackable = True
                                depth = head.depth + 1

                                hyp_tab_dep1 = atab.tl.hyp_tab[line1]
                                hyp_tab_dep2 = atab.tl.hyp_tab[line2]
                                tab_dep = get_tab_dep(hyp_tab_dep1, hyp_tab_dep2)

                                nd1, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                nd2, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                add_ancestors(nd2, nd1, head, None)
                                c1 = prevent_duplicates(screen, atab, nd1, nd2)

                                if c1:
                                    if not head.type:
                                        mark_hyp_inactive(tab_dep, head)
                                        unmark(tab_dep)

                                    progress = True
                                    
                                    done, partial = check_done(screen, atab, interface)
                                    if partial:
                                        old_bt_list = [] # reset backtracking 
                                    
                                    screen.debug("Hypothesis expansion")

                                if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False, atab.tl

                                check_lengths(atab.top_tab)
                                unmark(atab.top_tab)
                    
                                if done or progress:
                                    break

                if done or progress:
                    break

            if done:
                break

            if progress:
                continue

            # 12) Implication atomic predicate expansion

            for impl in impls:
                line2 = impl.line

                tree = tlist1[line2]
                atomic = find_atomic_predicates(screen, tree)
        
                if not atomic: # predicates at the top level would already have been expanded
                    continue

                libthms = filter_definitions3(screen, atab, index, ht, impl.const1, impl.const2, tabc)

                for title, filepos, line in libthms:
                    filtered_atomic, temp_tl, line = atomic_rewrite_possible(screen, atab, atomic, filepos, line)

                    if filtered_atomic:
                        # transfer library result to tableau
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line, defn=True)
                        
                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, impl.depth + 1, True, library=True)

                        if line1 not in impl.applied: # check we didn't already apply this expansion to this impl
                            impl.applied.append(line1) # mark as applied

                            n1 = len(tlist1) # any lines added after these are new
                            dirty1 = []
                            dirty2 = []

                            tcopy = deepcopy(tree) # we'll replace the original line with this
                    
                            for parent, n in filtered_atomic:
                                apply_atomic_rewrite(screen, atab, dirty1, dirty2, parent, n, n1, line1, line2)

                                progress = True

                            if progress:
                                tlist1[line2] = tcopy # switch original impl with copy
                                atab.hyp_impls.remove(impl) # remove original node from hyp_impls

                                depth = impl.depth + 1

                                hyp_tab_dep1 = atab.tl.hyp_tab[line1]
                                hyp_tab_dep2 = atab.tl.hyp_tab[line2]
                                tab_dep = get_tab_dep(hyp_tab_dep1, hyp_tab_dep2)

                                nd1, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                nd2, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                add_ancestors(nd2, nd1, impl, None)

                                if True: # c1 and c2:
                                    done, partial = check_done(screen, atab, interface)
                                    if partial:
                                        old_bt_list = [] # reset backtracking 
                                    
                                    screen.debug("Implication atomic predicate expansion")

                                if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False, atab.tl

                                check_lengths(atab.top_tab)
                                unmark(atab.top_tab)
                    
                                break
                if done or progress:
                    break

            if done:
                break

            if progress:
                continue

            # 13) Head atomic predicate expansion

            for head in heads:
                line2 = head.line

                tree = tlist1[line2]
                atomic = find_atomic_predicates(screen, tree)
        
                if not atomic: # predicates at the top level would already have been expanded
                    continue

                libthms = filter_definitions3(screen, atab, index, ht, head.const1, None, tabc)

                for title, filepos, line in libthms:
                    filtered_atomic, temp_tl, line = atomic_rewrite_possible(screen, atab, atomic, filepos, line)

                    if filtered_atomic:
                        # transfer library result to tableau
                        dirty1, dirty2, line1 = load_theorem(screen, atab, temp_tl, filepos, line, defn=True)
                        
                        impl = get_autonode(screen, atab.hyp_impls, line1)

                        update_autotab(screen, atab, atab.top_tab, dirty1, dirty2, interface, impl.depth + 1, True, library=True)

                        if line1 not in impl.applied: # check we didn't already apply this expansion to this impl
                            impl.applied.append(line1) # mark as applied

                            n1 = len(tlist1) # any lines added after these are new
                            dirty1 = []
                            dirty2 = []

                            tcopy = deepcopy(tree) # we'll replace the original line with this
                    
                            for parent, n in filtered_atomic:
                                apply_atomic_rewrite(screen, atab, dirty1, dirty2, parent, n, n1, line1, line2)

                                progress = True

                            if progress:
                                head.backtrackable = True
                                tlist1[line2] = tcopy # switch original head with copy
                                atab.hyp_heads.remove(head) # remove original node from hyp_heads

                                depth = head.depth + 1

                                hyp_tab_dep1 = atab.tl.hyp_tab[line1]
                                hyp_tab_dep2 = atab.tl.hyp_tab[line2]
                                tab_dep = get_tab_dep(hyp_tab_dep1, hyp_tab_dep2)
    
                                nd1, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                dirty1, dirty2 = autocleanup(screen, atab.tl, atab.ttree)
                                nd2, _ = update_autotab(screen, atab, tab_dep, dirty1, dirty2, interface, depth, False)
                                add_ancestors(nd2, nd1, head, None)

                                if True: # c1 and c2:
                                    done, partial = check_done(screen, atab, interface)
                                    if partial:
                                        old_bt_list = [] # reset backtracking 
                                    
                                    screen.debug("Predicate atomic predicate expansion")

                                if autotab_remove_deadnodes(screen, atab, heads, impls, interface):
                                    library.close()
                                    automation_limit += automation_increment
                                    return False, atab.tl

                                check_lengths(atab.top_tab)
                                unmark(atab.top_tab)
                    
                                break
                if done or progress:
                    break

            if done:
                break

            if progress:
                continue
            
            # 13) Hypothesis "backtracking"

            if True: # whether we want hypothesis backtracking
                for node in atab.hyps_active:
                    if not is_implication(tlist1[node.line]):
                        node.backtrackable = False

                if not old_bt_list:
                    bt_list = copy(atab.hyps_active)
                    old_bt_list = copy(bt_list)
                else:
                    bt_list = copy(old_bt_list)

                atab.hyps_active = copy(bt_list)

                checked = []

                while bt_list:
                    while bt_list:
                        node = bt_list.pop()
                        if not is_implication(tlist1[node.line]) and node.backtrackable:
                            atab.hyps_active.append(node)
                            progress = True
                            break
                        else:
                            checked.append(node)
                    
                    if progress:
                        break

                    while checked:
                        node = checked.pop()
                        for n in node.ancestors:
                            if n not in bt_list:
                                bt_list.append(n)

            if progress:
                continue
            
            screen.debug("Final failure")
            return False, atab.tl

    clear_screen(screen, atab.tl, interface)
    update_screen(screen, atab, interface)

    library.close()
    return True, atab.tl # all tableaus done


        