from utility import is_implication, get_constants, update_constraints, process_sorts, unquantify, \
     relabel, deps_defunct, vars_used, complement_tree, sorts_mark, sorts_rollback
from autoparse import parse_consts
from unification import unify
from nodes import DeadNode, AutoImplNode, AutoEqNode, AutoIffNode, ImpliesNode, AndNode, \
     SymbolNode, NeqNode, ForallNode, EqNode, NotNode, FnApplNode, ElemNode, VarNode, OrNode, \
     BoolNode
from tree import TreeList
from interface import line_limit
from copy import deepcopy
import logic

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

def create_constant_graph():
    """
    Creates the graph of constants, which is used to determine maximal constants. We say that
    a constant A is greater than B if A is defined in terms of B in a #definition in the library.
    For now we do this manually.
    """
    top_list = [ConstGraphNode('\\in'), ConstGraphNode('0'), ConstGraphNode('1'), \
                ConstGraphNode('[]'), ConstGraphNode('\\implies'), ConstGraphNode('\\emptyset'), \
                ConstGraphNode('True'), ConstGraphNode('False')] # start with just the undefined constants

    insert_constant(top_list, '\\subseteq', ['\\in', '\\implies'])
    insert_constant(top_list, '=', ['\\subseteq'])
    insert_constant(top_list, '\\neq', ['\\subseteq'])
    insert_constant(top_list, '\\subsetneq', ['=', '\\neq', '\\subseteq'])
    insert_constant(top_list, '\\emptyset', ['True', 'False'])
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
        defn_str = library.readline()[0:-1]
        success, defns = parse_consts(None, defn_str)
        tags = library.readline()[6:-1]
        filepos = library.tell()
        if filepos == loaded_theorem:
            break
        index.append((title, tags, consts, nconsts, defns, filepos))
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
    tlist[idx] = ImpliesNode(complement_tree(tlist[idx].left), tlist[idx].right)

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
        thm, univs = unquantify(None, thm, False)

        thm, _ = relabel(None, tl, univs, thm, True)
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
        thm, univs = unquantify(None, thm, False)

        prec, u = unquantify(None, thm.left, True)
        # check if precedent unifies with hyp
        unifies1, _, _ = unify(None, tl, prec, hyps[hidx2])

        if not unifies1:
            prec, u = unquantify(None, thm.right, True)
            # check if neg consequent unifies with hyp2
            comp = complement_tree(prec)
            unifies2, _, _ = unify(None, tl, comp, hyps[hidx2])

    return unifies1, unifies2

def modus_ponens(screen, tab, idx1, idx2, forward, library):
    hyps = tab.tl.tlist1.data

    # get dependency information
    dep = None
    
    if forward:
        if -1 in tab.tl.tlist1.dependency(idx1): # no dependencies for idx1
            dep = deepcopy(tab.tl.tlist1.dependency(idx2))
        elif -1 in tab.tl.tlist1.dependency(idx2): # no dependencies for idx2
            dep = deepcopy(tab.tl.tlist1.dependency(idx1))
        else: # dependencies for both idx1 and idx2
            dep = list(filter(lambda x : x in tab.tl.tlist1.dep[idx1], tab.tl.tlist1.dep[idx2]))

    success, dirty1, dirty2 = logic.modus_ponens(None, tab.tl, None, dep, idx1, [idx2], forward)
    
    if success:
        if not library:
            tab.hypotheses.remove(idx1)
            
        # update hypothesis and target lists and dependency information
        if forward:
            tab.hypotheses.remove(idx2)
            tab.hypotheses.append(dirty1[0])
        else:
            tab.targets.append(dirty2[0])

            # update dependency information
            for i in range(len(hyps)):
                if i in tab.tl.tlist1.dep: # we have dependency information for this hypothesis
                    dep = tab.tl.tlist1.dep[i]

                    if idx2 in dep: 
                        dep.remove(idx2) # remove old target from dependency list
                        dep += dirty2 # put new target in dependency list

    return success

def modus_tollens(screen, tab, idx1, idx2, forward, library):
    hyps = tab.tl.tlist1.data

    # get dependency information
    dep = None
    
    if forward:
        if -1 in tab.tl.tlist1.dependency(idx1): # no dependencies for idx1
            dep = deepcopy(tab.tl.tlist1.dependency(idx2))
        elif -1 in tab.tl.tlist1.dependency(idx2): # no dependencies for idx2
            dep = deepcopy(tab.tl.tlist1.dependency(idx1))
        else: # dependencies for both idx1 and idx2
            dep = list(filter(lambda x : x in tab.tl.tlist1.dep[idx1], tab.tl.tlist1.dep[idx2]))

    success, dirty1, dirty2 = logic.modus_tollens(None, tab.tl, None, dep, idx1, [idx2], forward)
    
    if success:
        if not library:
            tab.hypotheses.remove(idx1)
            
        # update hypothesis and target lists and dependency information
        if forward:
            tab.hypotheses.remove(idx2)
            tab.hypotheses.append(dirty1[0])
        else:
            tab.targets.append(dirty2[0])

            # update dependency information
            for i in range(len(hyps)):
                if i in tab.tl.tlist1.dep: # we have dependency information for this hypothesis
                    dep = tab.tl.tlist1.dep[i]

                    if idx2 in dep: 
                        dep.remove(idx2) # remove old target from dependency list
                        dep += dirty2 # put new target in dependency list

    return success

def expansion(screen, tab, defn_idx, idx, is_hyp, level):
    dirty1, dirty2 = logic.expansion(None, tab.tl, defn_idx, idx, is_hyp, level)
    hyps = tab.tl.tlist1.data

    # update hypothesis and target lists and dependency information
    if is_hyp:
        tab.hypotheses.remove(idx)
        tab.hypotheses.append(dirty1[0])
    else:
        tab.targets.append(dirty2[0])

        # update dependency information
        for i in range(len(hyps)):
            if i in tab.tl.tlist1.dep: # we have dependency information for this hypothesis
                dep = tab.tl.tlist1.dep[i]

                if idx in dep: 
                    dep.remove(idx) # remove old target from dependency list
                    dep += dirty2 # put new target in dependency list

def filter_theorems(screen, index, constant_graph, maximal_constants, forward):
    """
    Given a library index, filter for theorems which will not introduce a new maximal constant
    that are not definitions.
    """
    thms = [] # list of theorems
    
    for (title, tags, c, nc, defns, filepos) in index:
        thmlist = c[2]
        nthmlist = nc[2]
        tag_list = tags.split(' ')
        for line in range(len(thmlist)):
            thm = thmlist[line]
            nthm = nthmlist[line]
            if '#definition' not in tag_list and \
                  (isinstance(thm, AutoImplNode) or isinstance(thm, AutoIffNode)):
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

def filter_definitions(index, constant_graph, consts):
    """
    Given a library index, filter for definitions which could potentially apply to a target
    with the given constants.
    """
    defns = [] # list of definitions
    
    for (title, tags, c, nc, defs, filepos) in index:
        defn = defs[2][0]
        tag_list = tags.split(' ')
        if '#definition' in tag_list:
            dl = defn.left
            dr = defn.right
            if set(dl).issubset(consts):
                defns.append((title, defn, filepos))
                
    return defns

def autocleanup(tl, defn=False):
    dirty1, dirty2 = logic.cleanup(None, tl, None, defn)
    logic.fill_macros(None, tl)
    ok, error = update_constraints(None, tl)
    if ok:
        ok, error = process_sorts(None, tl)
        if not ok:
            raise Exception(error)
    else:
        raise Exception(error)

def temp_load_theorem(tab, library, filepos, line, defn=False):
    """
    Takes a filepos and line of a theorem to load and checks to see if we already loaded the theorem and
    if so returns a pair (tl, idx) where tl is the current tableau and idx is the index of the given line
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
        autocleanup(temp_tl, defn) # do cleanup moves on theorem (skolemize, metavars, expand iff, etc.)
        
        return temp_tl, line

def load_theorem(screen, tab, library, filepos, line, defn=False):
    """
    Takes a filepos and line of a theorem to load and loads it into the current tableau. Returns the index
    of the given line in the tableau.
    """
    if filepos not in tab.libthms_loaded:
        n = len(tab.tl.tlist1.data)
        logic.library_import(None, tab.tl, library, filepos)
        autocleanup(tab.tl, defn) # do cleanup moves on theorem (skolemize, metavars, expand iff, etc.)
        tab.libthms_loaded[filepos] = n
    else:
        n = tab.libthms_loaded[filepos]

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
        tl.tlist2.data.append(tab.tl.tlist2.data[tidx])
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
        tl.tlist1.data.append(tab.tl.tlist1.data[hidx])
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
                success = False # whether we successfully found a move to do
                
                twinned_targets = get_twinned_targets(tars, tab.targets) # make a list of all disjunctive targets

                # 0) Automated cleanup moves
                n1 = len(hyps)
                n2 = len(tars)
                v1, v2 = logic.cleanup(screen, tab.tl)

                update_screen(screen, qz, hyps, tars) # update the QZ, hyps and tars on the screen

                screen.dialog("Pause")
                
                if v1 == False: # display any errors from cleanup
                    screen.dialog(v2)
                    return False
                else: # update targets and hypotheses
                    for k in v1:
                        if k >= n1:
                            tab.hypotheses.append(k)
                    for k in v2:
                        if k >= n2:
                            tab.targets.append(k)

                # record hypothesis-target twins
                for j in tab.hypotheses:
                    dep_list = tab.tl.tlist1.dependency(j) # targets provable by hypothesis j

                    for k in twinned_targets:
                        if k in dep_list:
                            tab.twins.append((j, k))
                            dep_list.remove(k)
                            break

                # update constants cache for any new hypotheses or targets
                get_statement_constants(tab)

                # check if done
                proved = False
                
                for j in range(len(hyps)):
                    hyp = hyps[j]
                    dep_list = tab.tl.tlist1.dependency(j)

                    if tidx in dep_list or -1 in dep_list: # hypothesis can be used to prove target
                        proved = isinstance(hyp, BoolNode) and not hyp.value # is hypothesis False                     
                            
                        if not proved:
                            proved, _, _ = unify(screen, tl, hyp, tars[tidx]) # does hypothesis unify with target

                        if proved: # target proved
                            break
                
                if proved:
                    break

                # 1) Turn targets disjunctions into implications
                if is_disjunction(tars[tidx]):
                    dangling = find_dangling_vars(hyps, tab.hypotheses, tars, tab.targets)
                    dangling_to_left(tars[tidx], dangling) # move any dangling variables to left of conjunction
                    disjunction_to_implication(tars, tidx) # turn disjunction into implication

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
                            
                for hidx in tab.hypotheses:
                    if is_implication(hyps[hidx]):
                        if (hidx, tidx) not in tab.twins: # if statements are not twinned
                            mp, mt = backwards_reasoning_possible(tab.tl, hyps, tars, hidx, tidx) # check if backwards mp/mt possible
                            
                            if mp:
                                success = modus_ponens(screen, tab, hidx, tidx, False, False) # backwards modus ponens
                            elif mt:
                                success = modus_tollens(screen, tab, hidx, tidx, False, False) # backwards modus tollens

                            if success:
                                break

                if success:
                    break # must get new target

                # 3b) Forwards non-library reasoning
                            
                for hidx1 in tab.hypotheses:
                    if is_implication(hyps[hidx1]):
                        for hidx2 in tab.hypotheses:
                            if hidx2 != hidx1 and not is_implication(hyps[hidx2]):
                                mp, mt = forwards_reasoning_possible(tab.tl, hyps, hidx1, hidx2) # check if forwards mp/mt possible
                                
                                if mp:
                                    success = modus_ponens(screen, tab, hidx1, hidx2, True, False) # forwards modus ponens
                                elif mt:
                                    success = modus_tollens(screen, tab, hidx1, hidx2, True, False) # forwards modus tollens

                                if success:
                                    break

                        if success:
                            break

                if success:
                    continue

                # 4) Not required

                # 5a) Backwards library reasoning
                
                # get all theorems that won't introduce a new maximal constant
                libthms = filter_theorems(screen, index, constant_graph, tab.maximal_constants, False)

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

                            temp_hyps = tl.tlist1.data # hypothesis list from tl
                            temp_tars = tl.tlist2.data # target list from tl

                            mp, mt = backwards_reasoning_possible(tl, temp_hyps, temp_tars, thm_idx, tar_idx) # selected theorem unifies

                            if (not neg and mp) or (neg and mt):
                                # now check how many unifications we have in total
                                unification_count = 0 # count of unifications

                                for idx in matches:
                                    tar_idx = append_target(tab, tl, idx) # append target to tableau

                                    # update counts
                                    mpi, mti = backwards_reasoning_possible(tl, temp_hyps, temp_tars, thm_idx, tar_idx)
                                    
                                    if (not neg and mpi) or (neg and mti):
                                        unification_count += 1
                                    elif (not neg and not mpi) or (neg and not mti):
                                        nomatch_count += 1

                                sorts_rollback(None, tab.tl) # reset sorts in our tableau from theorem that was temporarily loaded

                                if unification_count > nomatch_count: # only continue if more matches than not
                                    # everything checks out, load the theorem into main tableau if not already there
                                    thm_idx = load_theorem(screen, tab, library, filepos, line)

                                    # apply result immediately
                                    if (not neg and mp):
                                        success = modus_ponens(screen, tab, thm_idx, tidx, False, True) # backwards modus ponens
                                    elif (neg and mt):
                                        success = modus_tollens(screen, tab, thm_idx, tidx, False, True) # backwards modus tollens
                            else:
                                sorts_rollback(None, tab.tl) # reset sorts in our tableau 

                            if success:
                                break

                if success:
                    break # must get new target

                # 5b) Forwards library reasoning
                
                # get all theorems that won't introduce a new maximal constant
                libthms = filter_theorems(screen, index, constant_graph, tab.maximal_constants, True)

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
                        
                        temp_hyps = tl.tlist1.data # hypothesis list from tl
                            
                        # check how many unifications we have in total
                        unifications = [] # hypotheses that unify

                        for idx in matches:
                            hyp_idx = append_hypothesis(tab, tl, idx) # append hypothesis to tableau

                            # update counts
                            mpi, mti = forwards_reasoning_possible(tl, temp_hyps, thm_idx, hyp_idx)
                            
                            if (not neg and mpi) or (neg and mti):
                                unifications.append((idx, mpi, mti))
                            elif (not neg and not mpi) or (neg and not mti):
                                nomatch_count += 1

                        sorts_rollback(None, tab.tl) # reset sorts in our tableau from theorem that was temporarily loaded

                        if len(unifications) > nomatch_count: # only continue if more matches than not
                            # everything checks out, load the theorem into main tableau if not already there
                            thm_idx = load_theorem(screen, tab, library, filepos, line)
                            (hidx, mp, mt) = unifications[0] # first unification

                            # apply result immediately
                            if (not neg and mp):
                                success = modus_ponens(screen, tab, thm_idx, hidx, True, True) # forwards modus ponens
                            elif (neg and mt):
                                success = modus_tollens(screen, tab, thm_idx, hidx, True, True) # forwards modus tollens

                    else:
                        sorts_rollback(None, tab.tl) # reset sorts in our tableau 

                    if success:
                        break

                if success:
                    continue

                # 6) Expand the target at the highest level
    
                tar_consts = tab.tconstants[tidx] # constants in the target
                
                # get all definitions that could possibly apply to target in theory
                libdefns = filter_definitions(index, constant_graph, tar_consts)

                for (title, defn, filepos) in libdefns:
                    tl, defn_idx = temp_load_theorem(tab, library, filepos, 0, True) # temp. load definition in same tableau as our target
                    tar_idx = append_target(tab, tl, tidx) # append our target to tableau if not already in there

                    level = logic.expansion(screen, tl, defn_idx, tar_idx, False)
                      
                    sorts_rollback(None, tab.tl) # reset sorts in our tableau from definition that was temporarily loaded

                    if level != None:
                        defn_idx = load_theorem(screen, tab, library, filepos, 0, True)

                        # apply result immediately
                        expansion(screen, tab, defn_idx, tidx, False, level)

                        success = True
                        break

                if success:
                    break # must get new target

                # 7) Expand a hypothesis at the highest level

                for hidx in tab.hypotheses:
                    hyp_consts = tab.hconstants[hidx] # constants in the hypothesis
                    
                    # get all definitions that could possibly apply to hypothesis in theory
                    libdefns = filter_definitions(index, constant_graph, hyp_consts)

                    for (title, defn, filepos) in libdefns:
                        tl, defn_idx = temp_load_theorem(tab, library, filepos, 0, True) # temp. load definition in same tableau as our hypothesis
                        hyp_idx = append_hypothesis(tab, tl, hidx) # append our hypothesis to tableau if not already in there

                        level = logic.expansion(screen, tl, defn_idx, hyp_idx, True)
                        
                        sorts_rollback(None, tab.tl) # reset sorts in our tableau from definition that was temporarily loaded

                        if level != None:
                            defn_idx = load_theorem(screen, tab, library, filepos, 0, True)

                            # apply result immediately
                            expansion(screen, tab, defn_idx, hidx, True, level)

                            success = True
                            break
                    if success:
                        break

                if success:
                    continue

                # no progress, exit automation with failure
                return False

    return True # all targets proved in all tableau
