from utility import is_implication, get_constants, get_init_vars, list_merge, deps_compatible, \
     TargetNode, update_constraints, process_sorts, append_tree, unquantify, target_compatible, \
     append_quantifiers, relabel, deps_defunct, is_duplicate_upto_metavars, metavars_used, \
     vars_used, max_type_size, complement_tree, sorts_mark, sorts_rollback, is_equality, \
     target_depends, get_constants_qz
from autoparse import parse_consts
from moves import check_targets_proved
from unification import unify, substitute
from nodes import DeadNode, AutoImplNode, AutoEqNode, AutoIffNode, ImpliesNode, AndNode, \
     SymbolNode, NeqNode, ForallNode, EqNode, NotNode, FnApplNode, ElemNode, VarNode, OrNode
from tree import TreeList
from interface import nchars_to_chars, iswide_char, line_limit
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

def create_constant_graph():
    """
    Creates the graph of constants, which is used to determine maximal constants. We say that
    a constant A is greater than B if A is defined in terms of B in a #definition in the library.
    For now we do this manually.
    """
    top_list = [ConstGraphNode('\\in'), ConstGraphNode('0'), ConstGraphNode('1'), ConstGraphNode('[]'), ConstGraphNode('\\implies')] # start with just the undefined constants

    insert_constant(top_list, '\\subseteq', ['\\in', '\\implies'])
    insert_constant(top_list, '=', ['\\subseteq'])
    insert_constant(top_list, '\\neq', ['\\subseteq'])
    insert_constant(top_list, '\\subsetneq', ['=', '\\neq', '\\subseteq'])
    insert_constant(top_list, '\\cup', ['\\in'])
    insert_constant(top_list, '\\cap', ['\\in'])
    insert_constant(top_list, 'Tuple(2)', ['=', '\\neq'])
    insert_constant(top_list, 'is_pair', ['0', '1', '=', '\\neq', 'Tuple(2)', '[]', '\\in'])
    insert_constant(top_list, '\\times', ['is_pair'])
    insert_constant(top_list, '\\mathcal{P}', ['\\subseteq'])
    insert_constant(top_list, 'complement', ['\\in'])
    insert_constant(top_list, '\\setminus', ['\\cap', 'complement'])    
    insert_constant(top_list, '{|}', ['\\in'])

    return top_list

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
        constants = get_constants(None, None, tree, constants)

    for tree in tars:
        constants = get_constants(None, None, tree, constants)

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
            
def get_statement_constants(tab):
    """
    Compute constants and negated constants for all non-implications in the tableau, starting
    from where we left off last time.
    """
    hyps = tab.tl.tlist1.data # hypothesis list
    tars = tab.tl.tlist2.data # target list

    for i in range(len(tab.hconstants), len(hyps)):
        if not is_implication(hyps[i]):
            tab.hconstants.append(get_constants(None, None, hyps[i])) # get constants of hypothesis
            tab.hnconstants.append(get_constants(None, None, complement_tree(hyps[i]))) # get negated constants of hypothesis
        else:
            tab.hconstants.append('') # make sure lists stay same length

    for i in range(len(tab.tconstants), len(tars)):
        tab.tconstants.append(get_constants(None, None, tars[i])) # get constants of target
        tab.tnconstants.append(get_constants(None, None, complement_tree(tars[i]))) # get negated constants of target

class Tableau:
    def __init__(self, tl, maximal_constants):
        self.tl = tl # data structure containing tl.tlist0 (QZ), tl.tlist1 (hypotheses), tl.tlist2 (targets)
        self.maximal_constants = maximal_constants # list of maximal constants in tableau
        self.libthms_loaded = dict() # keeps track of which library theorems we already loaded
        self.hypotheses = [i for i in range(len(tl.tlist1.data))] # list of hypotheses which have not been used or deleted
        self.targets = [i for i in range(len(tl.tlist2.data))] # list of targets which have not been proved or discarded
        self.twins = [] # list of twinned (hypothesis, target) pairs
        self.hconstants = [] # list of constants for each hypothesis
        self.hnconstants = [] # list of negated constants for each hypothesis
        self.tconstants = [] # list of constants for each target
        self.tnconstants = [] # list of negated constants for each target

def create_index(library, loaded_theorem):
    """
    Read the library in and create an index of all theorems and definitions up
    to but not including the theorem we are trying to prove.
    """
    index = []
    title = library.readline()
    while title: # check for EOF
        title = title[7:-1]
        const_str = library.readline()[0:-1]
        success, consts = parse_consts(None, const_str)
        nconst_str = library.readline()[0:-1]
        success, nconsts = parse_consts(None, nconst_str)
        tags = library.readline()[6:]
        filepos = library.tell()
        if filepos == loaded_theorem:
            break
        index.append((title, tags, consts, nconsts, filepos))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    return index

def clear_screen(screen):
    """
    Clear the QZ, hypothesis zone and target zone on the screen
    """
    screen.pad0.pad[0] = '' # clear QZ buffer
    screen.pad1.pad = ['' for i in range(0, line_limit)] # clear hypotheses buffer
    screen.pad2.pad = ['' for i in range(0, line_limit)] # clear targets buffer

    screen.pad0.refresh() # update QZ on screen
    screen.pad1.refresh() # update hypothesis zone on screen
    screen.pad2.refresh() # update target zone on screen

def update_screen(screen, qz, hyps, tars):
    """
    Update the screen with the information from the given QZ, hypothesis list and target list
    """
    if qz: # if qz is not empty
        screen.pad0.pad[0] = str(qz[0]) # insert information from QZ
    if hyps: # if hypothesis list not empty
        for i in range(len(hyps)):
            screen.pad1.pad[i] = str(hyps[i])
    if tars: # if hypothesis list not empty
        for i in range(len(tars)):
            screen.pad2.pad[i] = str(tars[i])

    # scroll to bottom of hypothesis pane
    screen.pad1.scroll_line = max(0, len(hyps) - screen.pad1.height)
    screen.pad1.cursor_line = len(hyps) - screen.pad1.scroll_line - 1
    
    # scroll to bottom of target pane
    screen.pad2.scroll_line = max(0, len(tars) - screen.pad2.height)
    screen.pad2.cursor_line = len(tars) - screen.pad2.scroll_line - 1
    
    screen.pad0.refresh() # update QZ on screen
    screen.pad1.refresh() # update hypothesis zone on screen
    screen.pad2.refresh() # update target zone on screen

def is_disjunction(tree):
    """
    Return True if given statement is a disjunction
    """
    return isinstance(tree, OrNode)

def find_dangling_vars(hyps, hyplist, tars, tarlist):
    duplicates = [] # variables that are duplicated
    dangling = [] # variables that only occur once

    for i in hyplist:
        var_list = vars_used(None, None, hyps[i], True)
        
        for var in var_list:
            if var not in duplicates:
                if var in dangling:
                    dangling.remove(var)
                    duplicates.append(var)
                else:
                    dangling.append(var)

    for i in tarlist:
        var_list = vars_used(None, None, tars[i], True)
        
        for var in var_list:
            if var not in duplicates:
                if var in dangling:
                    dangling.remove(var)
                    duplicates.append(var)
                else:
                    dangling.append(var)

    return dangling
    
def dangling_to_left(tree, dangling):
    """
    If there are only dangling variables on the right of the tree, switch the
    left and right sides of the tree so dangling vars are on the left.
    """
    var1 = vars_used(None, None, tree.left, True)

    if not any(v in dangling for v in var1):
        var2 = vars_used(None, None, tree.right, True)
    
        if any(v in dangling for v in var2):
            t = tree.left
            tree.left = tree.right
            tree.right = t

def disjunction_to_implication(tlist, idx):
    """
    Turn P \vee Q into ¬P => Q
    """
    tlist[idx] = ImpliesNode(complement_tree(tlist.idx[left]), tlist.idx[right])

def get_twinned_targets(tars, tarlist):
    twinned = [] # list of targets that are disjunctive
    
    for i in tarlist:
        if is_disjunction(tars[i]):
            twinned.append(i)

    return twinned
    
def backwards_reasoning_possible(tl, hyps, tars, hidx, tidx):
    unifies1 = False # whether backwards modus ponens is possible
    unifies2 = False # whether backwards modus tollens is possible
    
    dep = tl.tlist1.dependency(hidx) # get target dependencies of hypothesis

    if -1 in dep or tidx in dep: # target is compatible
        thm = hyps[hidx]

        thm, _ = relabel(None, tl, [], thm, True)
        prec, u = unquantify(None, thm.right, False)

        # check if precedent unifies with hyp (modus ponens possible)
        unifies1, _, _ = unify(None, tl, prec, tars[tidx])

        if not unifies1:
            prec, u = unquantify(None, thm.left, True)
            # check if complement of precedent unifies with hyp (modus tollens possible)
            unifies2, _, _ = unify(None, tl, complement_tree(prec), tars[tidx])

    return unifies1, unifies2

def forwards_reasoning_possible(tl, hyps, hidx1, hidx2):
    unifies1 = False # whether forwards modus ponens is possible
    unifies2 = False # whether forwards modus tollens is possible
    
    dep1 = tl.tlist1.dependency(hidx1) # get target dependencies of hypothesis
    dep2 = tl.tlist1.dependency(hidx2) # get target dependencies of hypothesis

    if -1 in dep1 or -1 in dep2 or any(i in dep1 for i in dep2): # targets are compatible
        thm = hyps[hidx1]

        prec, u = unquantify(None, thm.left, True)
        # check if precedent unifies with hyp
        unifies1, _, _ = unify(None, tl, prec, hyps[hidx2])

        if not unifies1:
            prec, u = unquantify(screen, thm.right, True)
            # check if neg consequent unifies with hyp2
            comp = complement_tree(prec)
            unifies2, _, _ = unify(None, tl, comp, hyps[hidx2])

    return unifies1, unifies2

def modus_ponens(tab, idx1, idx2, forward):
    hyps = tab.tl.tlist1.data

    # get dependency information
    if forward:
        if idx1 not in tab.tl.dep: # no dependencies for idx1
            if idx2 in tab.tl.dep: # dependencies for idx2
                dep = deepcopy(tab.tl.dep[idx2])
        elif idx2 not in tab.tl.dep: # no dependencies for idx2
            if idx1 in tab.tl.dep: # dependencies for idx1
                dep = deepcopy(tab.tl.dep[idx1])
        else: # dependencies for both idx1 and idx2
            dep = list(filter(lambda x : x in tab.tl.dep[idx1], tab.tl.dep[idx2]))
    else:
        dep = None

    success, dirty1, dirty2 = logic.modus_ponens(None, tl, None, dep, idx1, [idx2], forward)
    
    if success:
        tab.hypotheses.remove(idx1)
            
        # update hypothesis and target lists and dependency information
        if forward:
            tab.hypotheses.remove(idx2)
            tab.hypotheses.append(dirty1[0])
        else:
            tab.targets.remove(idx2)
            tab.targets.append(dirty2[0])

            # update dependency information
            for i in range(len(hyps)):
                if i in tab.tl.dep: # we have dependency information for this hypothesis
                    dep = tab.tl.dep[i]

                    if idx2 in dep: 
                        dep.remove(idx2) # remove old target from dependency list
                        dep += dirty2 # put new target in dependency list

    return success

def modus_tollens(tab, idx1, idx2, forward):
    hyps = tab.tl.tlist1.data

    # get dependency information
    if forward:
        if idx1 not in tab.tl.dep: # no dependencies for idx1
            if idx2 in tab.tl.dep: # dependencies for idx2
                dep = deepcopy(tab.tl.dep[idx2])
        elif idx2 not in tab.tl.dep: # no dependencies for idx2
            if idx1 in tab.tl.dep: # dependencies for idx1
                dep = deepcopy(tab.tl.dep[idx1])
        else: # dependencies for both idx1 and idx2
            dep = list(filter(lambda x : x in tab.tl.dep[idx1], tab.tl.dep[idx2]))
    else:
        dep = None

    success, dirty1, dirty2 = logic.modus_tollens(None, tl, None, dep, idx1, [idx2], forward)
    
    if success:
        tab.hypotheses.remove(idx1)
            
        # update hypothesis and target lists and dependency information
        if forward:
            tab.hypotheses.remove(idx2)
            tab.hypotheses.append(dirty1[0])
        else:
            tab.targets.remove(idx2)
            tab.targets.append(dirty2[0])

            # update dependency information
            for i in range(len(hyps)):
                if i in tab.tl.dep: # we have dependency information for this hypothesis
                    dep = tab.tl.dep[i]

                    if idx2 in dep: 
                        dep.remove(idx2) # remove old target from dependency list
                        dep += dirty2 # put new target in dependency list

    return success

def filter_theorems(index, constant_graph, maximal_constants, forward):
    """
    Given a library index, filter for theorems which will not introduce a new maximal constant
    that are not definitions.
    """
    thms = [] # list of theorems
    
    for (title, tags, c, nc, filepos) in index:
        thmlist = c[2]
        nthmlist = nc[2]
        tag_list = tags.split(' ')
        for line in range(len(thmlist)):
            thm = thmlist[line]
            nthm = nthmlist[line]
            if '#definition' not in tag_list and \
                  isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode):
                tcl = thm.left
                tcr = thm.right
                tncl = nthm.left
                tncr = nthm.right
                if forward: 
                    if check_maximal_constants(constant_graph, maximal_constants, tcr):
                        thms.append((title, thm, nthm, filepos, line, False))
                    if check_maximal_constants(constant_graph, maximal_constants, tncl):
                        thms.append((title, thm, nthm, filepos, line, True))
                else:
                    if check_maximal_constants(constant_graph, maximal_constants, tcl):
                        thms.append((title, thm, nthm, filepos, line, False))
                    if check_maximal_constants(constant_graph, maximal_constants, tncr):
                        thms.append((title, thm, nthm, filepos, line, True))
    return thms

def autocleanup(tl):
    dirty1, dirty2 = logic.cleanup(None, tl)
    logic.fill_macros(None, tl)
    ok, error = update_constraints(None, tl)
    if ok:
        ok, error = process_sorts(None, tl)
        if not ok:
            raise Exception(error)
    else:
        raise Exception(error)

def temp_load_theorem(tab, library, filepos, line):
    """
    Takes a filepos and line of a theorem to load and checks to see if we already loaded the theorem and
    if so returns a paid (tl, idx) where tl is the current tableau and idx is the index of the given line
    of the theorem. If not, we create a temporary tableau with the theorem present and return it and the
    corresponding index relative to that tableau.
    """
    if filepos in tab.libthms_loaded: # we have already loaded the theorem
        return tab.tl, tab.libthms_loaded[filepos] + line
    else: # we haven't loaded it, so create temporary tableau
        temp_tl = TreeList()
        temp_tl.vars = deepcopy(tab.tl.vars) # copy variable subscript record from tl
        temp_tl.stree = tab.tl.stree # copy sort tree from tl
        sorts_mark(None, tab.tl) # allow for rollback of sort graph
        logic.library_import(None, temp_tl, library, filepos)
        autocleanup(tab.tl) # do cleanup moves on theorem (skolemize, metavars, expand iff, etc.)
        
        return temp_tl, line

def load_theorem(tab, library, filepos, line):
    """
    Takes a filepos and line of a theorem to load and loads it into the current tableau. Returns the index
    of the given line in the tableau.
    """
    n = len(tab.tl.tlist1.data)
    logic.library_import(None, tab.tl, library, filepos)
    autocleanup(tab.tl) # do cleanup moves on theorem (skolemize, metavars, expand iff, etc.)
    tab.libthms_loaded[filepos] = n
    return n + line

def append_target(tab, tl, tidx):
    """
    If tl is the current tableau, simply return tidx. Else append the target tidx from the current tableau
    to the given tl and return its index.
    """
    if tab.tl == tl:
        return tidx
    else:
        n = len(tl.tlist2.data)
        tl.tlist2.data.append(tab.tl.tlist2[tidx])
        return n

def append_hypothesis(tab, tl, hidx):
    """
    If tl is the current tableau, simply return hidx. Else append the hypothesis idx from the current tableau
    to the given tl and return its index.
    """
    if tab.tl == tl:
        return hidx
    else:
        n = len(tl.tlist1.data)
        tl.tlist1.data.append(tab.tl.tlist1[hidx])
        return n

def automate(screen, tl):
    """
    The main automation function. Screen is where we are going to display the current tableau and tl is the
    data structure containing the initial quantifier zone, hypotheses and target.
    """
    # initial program setup
    constant_graph = create_constant_graph() # create the graph of constants
    maximal_constants = get_maximal_constants(constant_graph, tl) # compute the maximal constants in the tableau
    initial_tableau = Tableau(tl, maximal_constants) # create the initial tableau object
    tableau_list = [initial_tableau] # initial list of tableaus (each can be split by disjunctive hypotheses)
    get_statement_constants(initial_tableau) # compute the initial constants for the statements in the tableau
    library = open("library.dat", "r") # open the library file so it can be read
    index = create_index(library, tl.loaded_theorem) # create index of library entries up to but not including theorem being proved
    
    while tableau_list: # iterate while there are still tableaus that need proving
        tab = tableau_list.pop() # get next tableau from tableau list

        while tab.targets: # iterate while there are still unproven targets in this tableau
            tidx = tab.targets.pop() # get index of next unproven target
           
            qz   = tab.tl.tlist0.data # the quantifier zone for this tableau
            hyps = tab.tl.tlist1.data # the list of parsed hypotheses for this tableau
            tars = tab.tl.tlist2.data # the list of parsed targets for this tableau

            clear_screen(screen) # clear whatever tableau was being displayed
            update_screen(screen, qz, hyps, tars) # put the QZ, hyps and tars on the screen

            # main waterfall loop
            while True: # keep going until we get stuck or target is proved
                twinned_targets = get_twinned_targets(tars, tab.targets) # make a list of all disjunctive targets

                # 0) Automated cleanup moves
                v1, v2 = logic.cleanup(None, tab.tl)

                update_screen(screen, qz, hyps, tars) # update the QZ, hyps and tars on the screen

                if v1 == False: # display any errors from cleanup
                    screen.dialog(v2)
                    return False
                else: # update targets and hypotheses
                    tab.hypotheses += v1
                    tab.targets += v2

                # record hypothesis-target twins
                for j in tab.hypotheses:
                    dep_list = tl.tlist1.dependency(j) # targets provable by hypothesis j

                    for k in twinned_targets:
                        if k in dep_list:
                            tab.twins.append((j, k))
                            dep_list.remove(k)
                            break

                # update constants cache for any new hypotheses or targets
                get_statement_constants(tab)

                # check if done
                for hyp in hyps:
                    unifies, _, _ = unify(screen, tl, hyp, tars[tidx]) # does hypothesis unify with target

                    if unifies: # target proved
                        break

                # 1) Turn targets disjunctions into implications
                if is_disjunction(tars[tidx]):
                    dangling = find_dangling_vars(hyps, tab.hypotheses, tars, tab.targets)
                    dangling_to_left(tars[tidx], dangling) # move any dangling variables to left of conjunction
                    disjunction_to_implication(tars, idx) # turn disjunction into implication

                    continue

                # 2) Split tableau if hypothesis is disjunction
                found_hyp_disjunct = False # whether we found a disjunction
                
                for hidx in tab.hypotheses:
                    if is_disjunction(hyps[hidx]):
                        new_tab = deepcopy(tab)
                        tableau_list.append(new_tab)

                        # replace P \vee Q with P, ¬P \wedge Q
                        hyps[hidx] = hyps[hidx].left # P

                        hyps2 = new_tab.tl.tlist1.data
                        hyps2[hidx] = AndNode(complement_tree(hyps2[hidx].left), hyps2[hidx].right) # ¬P \wedge Q
                    
                        found_hyp_disjunct = True

                        break
                
                if found_hyp_disjunct:
                    continue

                # 3a) Backwards non-library reasoning
                success = False
                            
                for hidx in tab.hypotheses:
                    if is_implication(hyps[hidx]):
                        if (hidx, tidx) not in tab.twins: # if statements are not twinned
                            mp, mt = backwards_reasoning_possible(tab.tl, hyps, tars, hidx, tidx) # check if backwards mp/mt possible
                            
                            if mp:
                                success = modus_ponens(tab, hidx, tidx, False) # backwards modus ponens
                            elif mt:
                                success = modus_tollens(tab, hidx, tidx, False) # backwards modus tollens

                            if success:
                                break

                if success:
                    continue

                # 3b) Forwards non-library reasoning
                success = False
                            
                for hidx1 in tab.hypotheses:
                    if is_implication(hyps[hidx1]):
                        for hidx2 in tab.hypotheses:
                            if hidx2 != hidx1 and not is_implication(hyps[hidx2]):
                                mp, mt = forwards_reasoning_possible(tab.tl, hyps, hidx1, hidx2) # check if forwards mp/mt possible
                                
                                if mp:
                                    success = modus_ponens(tab, hidx1, hidx2, True) # forwards modus ponens
                                elif mt:
                                    success = modus_tollens(tab, hidx1, hidx2, True) # forwards modus tollens

                                if success:
                                    break

                        if success:
                            break

                if success:
                    continue

                # 4a) Backwards library reasoning
                success = False

                # get all theorems that won't introduce a new maximal constant
                libthms = filter_theorems(index, constant_graph, tab.maximal_constants, False)

                for (title, c, nc, filepos, line, neg) in libthms: # iterate over library theorems
                    implc = c.right # constants used in theorem
                    nimplc = nc.left # negated constants used in theorem
                    
                    # first check if it could even in theory apply to our target
                    tar_constants = tab.tconstants[tidx] # get constants used in our target
                    if (not neg and set(implc).issubset(tar_constants)) or (neg and set(nimplc).issubset(tar_constants)):
                        # optimization: first check how many statements could even in theory match the theorem
                        matches = [] # we'll actually collect statements that match
                        nomatch_count = 0 # number that couldn't possibly match

                        for idx in tab.targets:
                            tar_constants = tab.tconstants[idx] # constants of target

                            if (not neg and set(implc).issubset(tar_constants)) or (neg and set(nimplc).issubset(tar_constants)):
                                matches.append(idx) # store match
                            elif (not neg and not set(implc).issubset(tar_constants)) or (neg and not set(nimplc).issubset(tar_constants)):
                                nomatch_count += 1 # increment count of non-matches
                        
                        if len(matches) > nomatch_count: # exclude immediately if potential match count already too low
                            # first check if the selected theorem could even in theory unify with our target
                            tl, thm_idx = temp_load_theorem(tab, library, filepos, line) # temp. load thm in same tableau as our target
                            tar_idx = append_target(tab, tl, tidx) # append our target to tableau if not already in there

                            hyps = tl.tlist1.data # hypothesis list from tl
                            tars = tl.tlist2.data # target list from tl

                            mp, mt = backwards_reasoning_possible(tl, hyps, tars, thm_idx, tar_idx) # selected theorem unifies

                            if (not neg and mp) or (neg and mt):
                                # now check how many unifications we have in total
                                unification_count = 0 # count of unifications

                                for idx in matches:
                                    tar_idx = append_target(tab, tl, idx) # append target to tableau

                                    # update counts
                                    mpi, mti = backwards_reasoning_possible(tl, hyps, tars, thm_idx, tar_idx)
                                    
                                    if (not neg and mpi) or (neg and mti):
                                        unification_count += 1
                                    elif (not neg and not mpi) or (neg and not mti):
                                        nomatch_count += 1

                                sorts_rollback(None, tab.tl) # reset sorts in our tableau from theorem that was temporarily loaded

                                if unification_count > nomatch_count: # only continue if more matches than not
                                    # everything checks out, load the theorem into main tableau if not already there
                                    thm_idx = load_theorem(tab, library, filepos, line)

                                    # apply result immediately
                                    if (not neg and mp):
                                        success = modus_ponens(tab, thm_idx, tidx, False) # backwards modus ponens
                                    elif (neg and mt):
                                        success = modus_tollens(tab, thm_idx, tidx, False) # backwards modus tollens
                            else:
                                sorts_rollback(None, tab.tl) # reset sorts in our tableau 

                            if success:
                                break

                if success:
                    continue

                # 4b) Forwards library reasoning
                success = False

                # get all theorems that won't introduce a new maximal constant
                libthms = filter_theorems(index, constant_graph, tab.maximal_constants, True)

                for (title, c, nc, filepos, line, neg) in libthms: # iterate over library theorems
                    implc = c.left # constants used in theorem
                    nimplc = nc.right # negated constants used in theorem
                    
                    # optimization: first check how many statements could even in theory match the theorem
                    matches = [] # we'll actually collect statements that match
                    nomatch_count = 0 # number that couldn't possibly match

                    for idx in tab.hypotheses:
                        if not is_implication(tab.tl.tlist1.data[idx]): # if hypothesis is not an implication
                            hyp_constants = tab.hconstants[idx] # constants of target

                            if (not neg and set(implc).issubset(hyp_constants)) or (neg and set(nimplc).issubset(hyp_constants)):
                                matches.append(idx) # store match
                            elif (not neg and not set(implc).issubset(hyp_constants)) or (neg and not set(nimplc).issubset(hyp_constants)):
                                nomatch_count += 1 # increment count of non-matches
                    
                    if len(matches) > nomatch_count: # exclude immediately if potential match count already too low
                        tl, thm_idx = temp_load_theorem(tab, library, filepos, line) # temp. load thm in same tableau as our target
                        
                        hyps = tl.tlist1.data # hypothesis list from tl
                            
                        # check how many unifications we have in total
                        unifications = [] # hypotheses that unify

                        for idx in matches:
                            hyp_idx = append_hypothesis(tab, tl, idx) # append hypothesis to tableau

                            # update counts
                            mpi, mti = forwards_reasoning_possible(tl, hyps, thm_idx, hyp_idx)
                            
                            if (not neg and mpi) or (neg and mti):
                                unifications.append(idx)
                            elif (not neg and not mpi) or (neg and not mti):
                                nomatch_count += 1

                        sorts_rollback(None, tab.tl) # reset sorts in our tableau from theorem that was temporarily loaded

                        if len(unifications) > nomatch_count: # only continue if more matches than not
                            # everything checks out, load the theorem into main tableau if not already there
                            thm_idx = load_theorem(tab, library, filepos, line)
                            hidx = unifications[0] # first unification

                            # apply result immediately
                            if (not neg and mp):
                                success = modus_ponens(tab, thm_idx, hidx, True) # forwards modus ponens
                            elif (neg and mt):
                                success = modus_tollens(tab, thm_idx, hidx, True) # forwards modus tollens
                    else:
                        sorts_rollback(None, tab.tl) # reset sorts in our tableau 

                    if success:
                        break

                if success:
                    continue

                # no progress, exit automation with failure
                return False

    return True # all targets proved in all tableau





#        i = 0
#        made_progress = False
#        while i < len(tlist2):
#            start1 = 0 if starting else len(tlist1)  # used by incremental completion checking
#            start2 = 0 if starting else len(tlist2)
#            starting = False
#            while i < len(tlist2):
#                if not isinstance(tlist2[i], DeadNode):
#                    break
#                i += 1
#            if i >= len(tlist2):
#                break
#            tar = get_autonode(screen, atab.tar_heads, i)
#            tprogress = False # whether or not some progress is made on the target side
#            hprogress = False # whether some progress is made on the hypothesis side
#                # try to find a theorem that applies to the target
#            libthms = filter_theorems2(screen, index)
#            for (title, c, nc, filepos, line, iff) in libthms:
#                # check to see if thm already loaded
#                line2 = tar.line
#                unifies1 = False
#                unifies2 = False
#                unifies3 = False
#                if filepos in libthms_loaded:
#                    j = libthms_loaded[filepos] # get position loaded in tableau
#                    tnode = get_autonode(screen, atab.hyp_impls, j + line)
#                    if tnode and tar.line not in tnode.applied:
#                        tnode.applied.append(tar.line)
#                        thm = tlist1[j + line]
#                        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
#                        if isinstance(thm, ImpliesNode):
#                            thm, _ = relabel(screen, tl, univs, thm, True)
#                            prec, u = unquantify(screen, thm.right, False)
#                            if not isinstance(prec, AndNode):
#                                # check if precedent unifies with hyp
#                                unifies1, assign, macros = unify(screen, tl, prec, tlist2[line2])
#                            if not unifies1:
#                                prec, u = unquantify(screen, thm.left, True)
#                                if not isinstance(prec, AndNode):
#                                    # check if precedent unifies with hyp
#                                    unifies2, assign, macros = unify(screen, tl, complement_tree(prec), tlist2[line2])
#                        elif isinstance(thm, EqNode):
#                            unifies3, _, _ = logic.limited_equality_substitution(screen, tl, ttree, None, \
#                                                                        j + line, line2, False, True)
#                else: # library theorem not yet loaded
#                    fake_tl = TreeList()
#                    fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
#                    fake_tl.stree = tl.stree # copy sort tree from tl
#                    sorts_mark(screen, tl)
#                    logic.library_import(screen, fake_tl, library, filepos)
#                    autocleanup(screen, fake_tl, fake_ttree)
#                    thm = fake_tl.tlist1.data[line]
#                    thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
#                    thm, _ = relabel(screen, fake_tl, univs, thm, True)
#                    if isinstance(thm, ImpliesNode):
#                        prec, u = unquantify(screen, thm.right, False)
#                        # check theorem has only one precedent
#                        if not isinstance(prec, AndNode):
#                            # check if precedent unifies with hyp
#                            unifies1, assign, macros = unify(screen, fake_tl, prec, tlist2[line2])
#                        if not unifies1:
#                            prec, u = unquantify(screen, thm.left, True)
#                            unifies2, assign, macros = unify(screen, fake_tl, complement_tree(prec), tlist2[line2])
#                    elif isinstance(thm, EqNode):
#                        fake_tl.tlist2.data.append(tlist2[line2])
#                        unifies3, _, _ = logic.limited_equality_substitution(screen, fake_tl, ttree, None, \
#                                                                        line, len(fake_tl.tlist2.data) - 1, False, True)
#                        del fake_tl.tlist2.data[len(fake_tl.tlist2.data) - 1]
#                    if unifies1 or unifies2 or unifies3:
#                        # transfer library result to tableau
#                        dirty1 = []
#                        dirty2 = []
#                        j = len(tlist1)
#                        fake_tlist0 = fake_tl.tlist0.data
#                        if fake_tlist0:
#                            append_quantifiers(tl.tlist0.data, fake_tlist0[0])
#                        fake_list1 = fake_tl.tlist1.data
#                        for k in range(len(fake_list1)):
#                            append_tree(tlist1, fake_list1[k], dirty1)
#                        libthms_loaded[filepos] = j
#                        tl.vars = fake_tl.vars
#                        tl.stree = fake_tl.stree
#                        update_autotab(screen, tl, atab, dirty1, dirty2, interface)
#                        tnode = get_autonode(screen, atab.hyp_impls, j + line)
#                        tnode.applied.append(tar.line)
#                    else:
#                        sorts_rollback(screen, tl)
#                if unifies1 or unifies2 or unifies3:
#                    line1 = j + line
#                    # apply modus ponens
#                    dep = tl.tlist1.dependency(line1)
#                    dep = target_compatible(screen, tl, ttree, dep, line2, False)
#                    if dep:
#                        n1 = len(tl.tlist1.data)
#                        n2 = len(tl.tlist2.data)
#                        if unifies1 or unifies2 or unifies3:
#                            if unifies1:
#                                success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], False)
#                            elif unifies2:
#                                success, dirty1, dirty2 = logic.modus_tollens(screen, tl, ttree, dep, line1, [line2], False)
#                            elif unifies3:
#                                success, dirty1, dirty2 = logic.limited_equality_substitution(screen, tl, ttree, dep, line1, line2, False, False)
#                            if success:
#                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
#                                dirty1, dirty2 = autocleanup(screen, tl, ttree)
#                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
#                                update_screen(screen, tl, interface, dirty1, dirty2)
#                                c1 = check_duplicates(screen, tl, ttree, n1, n2, i, interface)
#                                if c1:
#                                    tprogress = True
#                                if autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
#                                    library.close()
#                                    automation_limit += automation_increment
#                                    return False
#                                break
#            if tprogress:
#                continue
#            # find all target compatible hypotheses
#            hyps = []
#            for v in atab.hyp_heads:
#                if deps_compatible(screen, tl, ttree, i, v.line):
#                    hyps.append(v)
#            # find all consequences of individual hypotheses (Fredy's ball)
#            for hyp in hyps:
#                line2 = hyp.line
#                hc = hyp.const1
#                # first check if any hyp_impls can be applied to head
#                for imp in atab.hyp_impls:
#                    line1 = imp.line
#                    if line1 < hyp.impls_done:
#                        continue
#                    hyp.impls_done = line1 + 1
#                    unifies1 = False
#                    unifies2 = False
#                    unifies3 = False
#                    if True: # ensure not applying metavar thm to metavar head
#                        thm = tlist1[line1]
#                        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
#                        if isinstance(thm, ImpliesNode):
#                            if True:
#                                prec, u = unquantify(screen, thm.left, True)
#                                if not isinstance(prec, AndNode):
#                                    # check if precedent unifies with hyp
#                                    unifies1, assign, macros = unify(screen, tl, prec, tlist1[line2])
#                            if True:
#                                prec, u = unquantify(screen, thm.right, True)
#                                if not isinstance(prec, AndNode):
#                                    # check if neg consequent unifies with hyp
#                                    comp = complement_tree(prec)
#                                    unifies2, assign, macros = unify(screen, tl, comp, tlist1[line2])
#                        elif isinstance(thm, EqNode):
#                            unifies3, _, _ = logic.limited_equality_substitution(screen, tl, ttree, None, \
#                                                                        line1, line2, True, True)
#                    if unifies1 or unifies2 or unifies3:
#                        # apply modus ponens and or modus tollens
#                        dep = tl.tlist1.dependency(line1)
#                        dep = target_compatible(screen, tl, ttree, dep, line2, True)
#                        if dep:
#                            success = False
#                            n1 = len(tl.tlist1.data)
#                            if unifies1:
#                                success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], True)
#                            if not success and unifies2:
#                                success, dirty1, dirty2 = logic.modus_tollens(screen, tl, ttree, dep, line1, [line2], True)
#                            if unifies3:
#                                success, dirty1, dirty2 = logic.limited_equality_substitution(screen, tl, ttree, dep, line1, line2, True, False)
#                            if success:
#                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
#                                dirty1, dirty2 = autocleanup(screen, tl, ttree)
#                                update_autotab(screen, tl, atab, dirty1, dirty2, interface)
#                                update_screen(screen, tl, interface, dirty1, dirty2)
#                                c1 = check_duplicates(screen, tl, ttree, n1, len(tlist2), i, interface)
#                                c2 = check_trivial(screen, tl, atab, n1, interface)
#                                if c1 and c2:
#                                    hprogress = True
#                                if autotab_remove_deadnodes(screen, tl, atab, n1, len(tlist2), interface):
#                                    library.close()
#                                    automation_limit += automation_increment   
#                                    return False
#                                break
#                # if no progress, look for library result that can be applied to head
#                if hprogress:
#                    continue
#                libthms = filter_theorems1(screen, index)
#                for (title, c, nc, filepos, line) in libthms:
#                    if filepos < hyp.filepos_done or (filepos == hyp.filepos_done and line < hyp.line_done):
#                        continue
#                    hyp.filepos_done = filepos
#                    hyp.line_done = line + 1
#                    # check to see if thm already loaded
#                    unifies1 = False
#                    unifies2 = False
#                    unifies3 = False
#                    if filepos not in libthms_loaded: # theorem not already loaded
#                        fake_tl = TreeList()
#                        fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
#                        fake_tl.stree = tl.stree # copy sort tree from tl
#                        sorts_mark(screen, tl)
#                        logic.library_import(screen, fake_tl, library, filepos)
#                        autocleanup(screen, fake_tl, fake_ttree)
#                        thm = fake_tl.tlist1.data[line]
#                        # check theorem has only one precedent
#                        thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
#                        if isinstance(thm, ImpliesNode):
#                            prec, u = unquantify(screen, thm.left, True)
#                            if not isinstance(prec, AndNode):
#                                # check if precedent unifies with hyp
#                                if True: # ensure not applying metavar thm to metavar head
#                                    unifies1, assign, macros = unify(screen, fake_tl, prec, tlist1[line2])
#                            if not unifies1:
#                                prec, u = unquantify(screen, thm.right, False)
#                                if not isinstance(prec, AndNode):
#                                    # check if precedent unifies with hyp
#                                    if True: # ensure not applying metavar thm to metavar head
#                                        unifies2, assign, macros = unify(screen, fake_tl, complement_tree(prec), tlist1[line2])
#                        elif isinstance(thm, EqNode):
#                            fake_tl.tlist1.data.append(tlist1[line2])
#                            unifies3, _, _ = logic.limited_equality_substitution(screen, fake_tl, ttree, None, \
#                                                                            line, len(fake_tl.tlist1.data) - 1, True, True)
#                            del fake_tl.tlist1.data[len(fake_tl.tlist1.data) - 1]
#                        if unifies1 or unifies2 or unifies3:
#                            # transfer library result to tableau
#                            hprogress = True
#                            dirty1 = []
#                            dirty2 = []
#                            j = len(tlist1)
#                            fake_tlist0 = fake_tl.tlist0.data
#                            if fake_tlist0:
#                                append_quantifiers(tl.tlist0.data, fake_tlist0[0])
#                            fake_list1 = fake_tl.tlist1.data
#                            for k in range(len(fake_list1)):
#                                append_tree(tlist1, fake_list1[k], dirty1)
#                            libthms_loaded[filepos] = j
#                            tl.vars = fake_tl.vars
#                            tl.stree = fake_tl.stree
#                            update_autotab(screen, tl, atab, dirty1, dirty2, interface)
#                            tnode = get_autonode(screen, atab.hyp_impls, j + line)
#                            tnode.applied.append((hyp.line, True))
#                        else:
#                            sorts_rollback(screen, tl)
#                if hprogress:
#                    break
#                # see if there are any theorems/defns to load which are not implications
#                libthms = filter_theorems3(screen, index)
#                for (title, c, nc, filepos, line) in libthms:
#                    headc = c[2][line]
#                    # check to see if thm already loaded, if not, load it
#                    if filepos not in libthms_loaded:
#                        hprogress = True
#                        logic.library_import(screen, tl, library, filepos)
#                        n1 = len(tl.tlist1.data)
#                        n2 = len(tl.tlist1.data)       
#                        j = len(tl.tlist1.data) - 1
#                        update_autotab(screen, tl, atab, [j], [], interface)
#                        libthms_loaded[filepos] = j
#                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
#                        update_autotab(screen, tl, atab, dirty1, dirty2, interface)
#                        update_screen(screen, tl, interface, dirty1, dirty2)
#                        if autotab_remove_deadnodes(screen, tl, atab, n1, n2, interface):
#                            library.close()
#                            automation_limit += automation_increment
#                            return False
#            dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree, start1, start2)
#            update_screen(screen, tl, interface, dirty1, dirty2)
#            if done:
#                return True
#            i += 1
#            if hprogress or tprogress:
#                made_progress = True
#        if not made_progress: # we aren't getting anywhere
#            update_screen(screen, tl, interface, None, None)
#            library.close()
#            automation_limit += 150
#            return False

        