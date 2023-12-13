from copy import deepcopy, copy
from nodes import ForallNode, ExistsNode, ImpliesNode, IffNode, VarNode, EqNode, \
     NeqNode, LtNode, GtNode, LeqNode, GeqNode, OrNode, AndNode, NotNode, \
     FnApplNode, LRNode, LeafNode, TupleNode, EqNode, ElemNode, UnionNode, \
     IntersectNode, DiffNode, CartesianNode, SymbolNode, SetBuilderNode, \
     NaturalNode, ExpNode, AddNode, SubNode, MulNode, DivNode, \
     SubseteqNode, SubsetneqNode, SupseteqNode, SupsetneqNode, \
     CircNode, NegNode, AbsNode, LambdaNode, PowerSetNode, \
     LtNode, GtNode, LeqNode, GeqNode, BoolNode, TupleComponentNode, SetOfNode, \
     DeadNode
from sorts import FunctionConstraint, CartesianConstraint, DomainTuple, SetSort, \
     NumberSort, TupleSort, PredSort, Universum, Sort
from typeclass import ValuedFieldClass, SemiringClass, MonoidClass, \
     OrderedSemiringClass, CompleteOrderedFieldClass, CompleteValuedFieldClass, \
     CompleteOrderedValuedFieldClass, FieldClass, OrderedRingClass, PosetClass
from unification import unify, subst, trees_unify, is_predicate, \
     is_function_type, check_macros, substitute
from utility import unquantify, relabel, append_tree, \
     append_tree2, replace_tree, replace_tree2, add_sibling, add_descendant, \
     skolemize_quantifiers, skolemize_statement, insert_sort, target_compatible, \
     target_depends, deps_defunct, deps_intersect, deps_compatible, \
     complement_tree, tags_to_list, canonicalise_tags, filter_titles, \
     trim_spaces, find_all, find_start_index, metavars_used, target_metavars, \
     domain, codomain, universe, system_unary_functions, \
     system_binary_functions, system_predicates, list_merge, get_constraint, \
     get_constants, merge_lists, process_constraints, get_terms, get_init_vars, \
     sorts_compatible, coerce_sorts, sorts_equal
import logic

from editor import edit
from parser import to_ast
from interface import nchars_to_chars

def annotate_ttree(screen, tl, ttree, hydras, tarmv):
    """
    Goes through the target dependency tree, ttree, and annotates each node
    with a list (called unifies) of hypotheses that unify with the associated
    target. In addition to this, a -1 indicates that the associated target is
    an equality the sides of which unify with each other.
    Furthermore, a pair (i, j) indicates a pair of hypotheses that unify to
    the negation of one another which are target compatible with the given
    target.
    If such an annotation is made and the list of metavariables used in the
    associated target is not a current hydra, add it to the list of hydras.
    In the case of contradictions, we check that no additional metavariables
    appear in the hypotheses i and j that don't appear in the target. To
    enable this, the function must be supplied with a list, tarmv, of the
    metavariables used in targets.
    The function not only appends the list of unifications to the target
    dependency tree nodes but also returns a list of the counts of such
    unifications and a list of lists of the unifications in the format we
    just described, one list for each target in numerical order (numbered
    from zero).
    """
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    ttree_full = ttree
    unification_count = [0 for i in range(len(tlist2))]
    unifications = [[] for i in range(len(tlist2))]
    
    def mark(ttree):
        if ttree.proved:
            return
        if ttree.num != -1:
            ttree.unifies = []
            for i in range(len(tlist1)):
                if deps_compatible(screen, tl, ttree_full, ttree.num, i):
                    unifies, assign, macros = unify(screen, tl, tlist2[ttree.num], tlist1[i])
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if unifies:
                        ttree.unifies.append(i)
                        unification_count[ttree.num] += 1
                        unifications[ttree.num].append(i)
                        if ttree.metavars not in hydras:
                            hydras.append(ttree.metavars)
            if isinstance(tlist2[ttree.num], EqNode): # equality may be a tautology
                unifies, assign, macros = unify(screen, tl, tlist2[ttree.num].left, tlist2[ttree.num].right)
                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                if unifies:
                    ttree.unifies.append(-1) # -1 signifies tautology P = P
                    unification_count[ttree.num] += 1
                    unifications[ttree.num].append(-1)
                    if ttree.metavars not in hydras:
                        hydras.append(ttree.metavars)
            for i in range(len(tlist1)):
                if deps_compatible(screen, tl, ttree_full, ttree.num, i): # a contradiction to hyp i would prove this target
                    tree1 = complement_tree(tlist1[i])
                    mv1 = metavars_used(tlist1[i])
                    for j in range(len(tlist1)):
                        if i != j:
                            di = deps_intersect(screen, tl, ttree_full, i, j)
                            dep_ok = False
                            for d in di:
                                if target_depends(screen, tl, ttree_full, ttree.num, d):
                                    dep_ok = True # ttree.num is a descendent of d
                                    break
                            if dep_ok: # this contradiction can prove target ttree.num
                                tree2 = tlist1[j]
                                unifies, assign, macros = unify(screen, tl, tree1, tree2)
                                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                                if unifies:
                                    mv2 = metavars_used(tlist1[j])
                                    if all(var in ttree.metavars or var not in tarmv for var in mv1) and \
                                       all(var in ttree.metavars or var not in tarmv for var in mv2): # check no additional mvars involved
                                        ttree.unifies.append((i, j)) # (i, j) signifies a contradiction between hyps i and j
                                        unification_count[ttree.num] += 1
                                        unifications[ttree.num].append((i, j))
                                        if ttree.metavars not in hydras:
                                            hydras.append(ttree.metavars)
                    
        for t in ttree.andlist:
            mark(t)
    
    mark(ttree)
    return unification_count, unifications

def generate_pairs(V, L, r, i=0, last_chosen_c=None):
    """
    Creates a generator for iterating through all possible ways of closing
    targets. A target can only close if it belongs to a set of targets which
    are all satisfied (either by matching a hypothesis, being proved by a
    contradiction in the hypotheses or being an equality which is a tautology)
    and the collective metavariables for which, do not appear elsewhere, and
    can all be filled in via unification in a consistent way.
    Of course, it may be that one such target is not a leaf in the target
    dependency tree. In such a case, we are happy to prove that target, instead
    of all its descendants in the tree, which creates a combinatorial explosion
    in the number of ways to prove targets.

    Here is a description of how this function works:
    V is a list of nonempty lists. The length of V is r. Each list in V is a list
    of indices in the range 0 to m - 1 inclusive. List L is a list of indices.

    This function creates a generator for iterating over all lists S of pairs of
    integers (c, d) defined as follows. The list S has length r. S[i] is a pair
    of integers (c_i, d_i) as follows. The index c_i should be one of the integers
    of V[i]. However, its index in V[i] should exceed that of the greatest index
    j for which V[i][j] = c_k for some k < i. The integer d_i should be some
    integer in the range 0 to L[c_i] - 1 inclusive.

    The interpretation is as follows. The list item L[j] is a count of the number
    of different unifications that could prove target j. The list item V[i] is a
    list of targets that could be proved which would suffice to prove the i-th
    target of some list of targets we've identified as being able to be proved
    as a block (taking into account metavariables).

    TODO: It's not clear that the condition to pick the c_i from the tail of the
    V[i] not containing any previous c_k's is correct. If a c_i is picked which
    is common to two V[i] lists then it proves both of the targets, but this
    algorithm wouldn't seem to allow for both targets to be proved solely by
    proving this one common target. Presumably the extra condition was added to
    reduce complexity, but perhaps it should at least allow the same c_i to be
    picked more than once.
    """
    if last_chosen_c is None:
        last_chosen_c = []
    if i == r:
        yield []
    else:
        start_index = find_start_index(V[i], set(last_chosen_c))
        for c_index in range(start_index, len(V[i])):
            c = V[i][c_index]
            last_chosen_c.append(c)
            for d in range(L[c]):
                for rest in generate_pairs(V, L, r, i + 1, last_chosen_c):
                    yield [(c, d)] + rest
            last_chosen_c.remove(c)

def find_hydra_heads(screen, tl, ttree, hydras_done, hydras_todo, hydra):
    """
    A hydra is essentially a list of metavariables which are connected because
    they appear in common targets. One can prove a target only if one can prove
    all the targets using metavariables in a hydra.
    A head of the hydra is a path from the bottom of the target dependency tree
    all the way to a leaf node that passes through a node making use of one of
    the metavariables in the given hydra.
    This function finds all the heads of a given hydra.
    Along the way, this function may discover hydras that we don't know about.
    This occurs when some path has a node with a metavariable appearing in the
    current hydra, but there are other nodes in the path with metavariables
    that would require expanding the current hydra. The new hydra so created
    is added to the list of hydras_todo, assuming it is not already in the list
    of hydras_done.
    """
    hydra_heads = []

    def find(ttree, path, head_found, head_killable):
        head_found = head_found or any(item in hydra for item in ttree.metavars)
        mv_ok = all(item in hydra for item in ttree.metavars)
        if ttree.unifies and mv_ok:
            path.append(ttree.num)
            head_killable = True
        if not mv_ok:
            merged = list_merge(hydra, ttree.metavars)
            if merged not in hydras_done and merged not in hydras_todo:
                hydras_todo.append(merged)
        if not ttree.andlist: # we are at a leaf node
            if not head_found: # this path does not concern us
                return True
            if not head_killable:
                return False
            hydra_heads.append(deepcopy(path))
            return True        
        for t in ttree.andlist:
             p = len(path)
             killable = find(t, path, head_found, head_killable)
             if not killable:
                 return False
             while len(path) > p:
                 path.pop()
        return True

    if find(ttree, [], False, False):
        return hydra_heads
    else:
        return []

def try_unifications(screen, tl, ttree, unifications, gen):
    """
    Given a list gen of pairs (c, d) each consisting of a target c and a list d
    of unifications that might prove this target, try to do the unifications in
    the list in a compatible way (wrt metavariable assignments coming from the
    unifications). If such a unification is possible, mark all the targets in
    the list as proved. Each of the unifications could be a unification of a
    target with a hypothesis, unification of a hypothesis with the negation of
    another or unification of two sides of a target that is an equality.
    """
    dirty1 = []
    dirty2 = []
    plist = []
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    for v in gen: # list of pairs (c, d) where c = targ to unify, d is index into list of hyps that it may unify with (or pair)
        assign = []
        unifies = False
        for (c, d) in v:
            hyp = unifications[c][d]
            if isinstance(hyp, tuple):
                (i, j) = hyp
                tree1 = complement_tree(tlist1[i])
                tree2 = tlist1[j]
                unifies, assign, macros = unify(screen, tl, tree1, tree2, assign)
            else:
                if isinstance(tlist2[c], DeadNode):
                    unifies = False
                    break
                if hyp == -1: # signifies tautology P = P
                    unifies, assign, macros = unify(screen, tl, tlist2[c].left, tlist2[c].right, assign)
                else:
                    if isinstance(tlist1[hyp], DeadNode):
                        unifies = False
                        break
                    unifies, assign, macros = unify(screen, tl, tlist2[c], tlist1[hyp], assign)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
            if not unifies:
                break
        if unifies:
            for (c, d) in v:
                d1, d2, pl = mark_proved(screen, tl, ttree, c)
                dirty1 += d1
                dirty2 += d2
                plist += pl
    return dirty1, dirty2, plist
                
def check_zero_metavar_unifications(screen, tl, ttree, tarmv):
    """
    Some targets do not contain metavariables, and when these can be unified
    with a hypothesis that doesn't involve metavariables used in other targets
    then this should be done. This function is needed as a special case because
    the general machinery works on hydras, which are non-empty lists of
    metavariables. As per the general machinery, a proof of a target in this
    way could involve either unification with a hypothesis, contradiction of
    two hypotheses or a target which is an equality with both sides the same.
    """
    dirty1 = []
    dirty2 = []
    plist = []
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    for i in range(len(tlist1)):
        mv1 = metavars_used(tlist1[i])
        if not any(v in tarmv for v in mv1):
            for j in range(len(tlist2)):
                mv2 = metavars_used(tlist2[j])
                if not any(v in tarmv for v in mv2):
                    if deps_compatible(screen, tl, ttree, j, i):
                        unifies, assign, macros = unify(screen, tl, tlist1[i], tlist2[j])
                        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                        if unifies:
                            d1, d2, pl = mark_proved(screen, tl, ttree, j)
                            dirty1 += d1
                            dirty2 += d2
                            plist += pl
    d1, d2, pl = check_contradictions(screen, tl, ttree, tarmv)
    dirty1 += d1
    dirty2 += d2
    plist += pl
    for i in range(len(tlist2)):
        if isinstance(tlist2[i], EqNode):
            if not metavars_used(tlist2[i]):
                unifies, assign, macros = unify(screen, tl, tlist2[i].left, tlist2[i].right)
                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                if unifies:
                    d1, d2, p1 = mark_proved(screen, tl, ttree, i)
                    dirty1 += d1
                    dirty2 += d2
                    plist += pl
    return dirty1, dirty2, plist

def mark_proved(screen, tl, ttree, n):
    """
    Given a target dependency tree, ttree, mark target n within this tree as
    proved, along with all the descendents of that node. Also set all
    hypotheses that can only be used to prove now proven nodes, to DeadNode
    (which shows up as a dashed line in the tableau) along with all the now
    proven nodes.
    """
    dirty1 = []
    dirty2 = []
    plist = [] # list of targets proved

    def process(dirty1, dirty2, plist, ttree, n):
        if ttree.num == n:
            if not ttree.proved:
                ttree.proved = True
                if n >= 0:
                    plist.append(ttree.num)
                for i in range(0, len(tl.tlist1.data)):
                    if deps_defunct(screen, tl, ttree, n, i):
                        tl.tlist1.data[i] = DeadNode(tl.tlist1.data[i])
                        dirty1.append(i)
                screen.pad1.refresh()
                for i in range(0, len(tl.tlist2.data)):
                    if target_depends(screen, tl, ttree, i, n): 
                        tl.tlist2.data[i] = DeadNode(tl.tlist2.data[i])
                        dirty2.append(i)
            return True
        for P in ttree.andlist:
            if process(dirty1, dirty2, plist, P, n):
                if all(t.proved for t in ttree.andlist) and not ttree.proved:
                    ttree.proved = True
                    if ttree.num >= 0:
                        plist.append(ttree.num)
                    for i in range(0, len(tl.tlist2.data)):
                        if deps_defunct(screen, tl, ttree, ttree.num, i):
                            tl.tlist1.data[i] = DeadNode(tl.tlist1.data[i])
                            dirty1.append(i)
                    for i in range(0, len(tl.tlist2.data)):
                        if target_depends(screen, tl, ttree, i, ttree.num): 
                            tl.tlist2.data[i] = DeadNode(tl.tlist2.data[i])
                            dirty2.append(i)
                return True
        return False

    process(dirty1, dirty2, plist, ttree, n)
    return dirty1, dirty2, plist

def check_contradictions(screen, tl, ttree, tarmv):
    """
    Check for any contradictions amongst hypotheses that don't involve metavars
    in the list tarmv (taken to be a list of all metavars appearing in
    targets). Mark any targets proved for which the contradicting hypotheses
    are target compatible.
    """
    dirty1 = []
    dirty2 = []
    plist = []
    tlist1 = tl.tlist1.data
    for i in range(len(tlist1)):
        mv1 = metavars_used(tlist1[i])
        if not any(v in tarmv for v in mv1):
            tree1 = complement_tree(tlist1[i])
            for j in range(0, i):
                mv2 = metavars_used(tlist1[j])
                if not any(v in tarmv for v in mv2):
                    di = deps_intersect(screen, tl, ttree, i, j)
                    if di: # hyps i and j can be used to prove targets
                        tree2 = tlist1[j]
                        unifies, assign, macros = unify(screen, tl, tree1, tree2)
                        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                        if unifies: # we found a contradiction
                            for t in di:
                                d1, d2, pl = mark_proved(screen, tl, ttree, t)
                                dirty1 += d1
                                dirty2 += d2
                                plist += pl
    return dirty1, dirty2, plist

def targets_proved(screen, tl, ttree):
    """
    This is the main wrapper which is called every move to see if we are done.
    First it computes all metavariables used in the targets. It then checks a
    special case of targets that can be proved without assigning any
    metavariables that occur in targets. It then annotates the target
    dependency tree with information about unifications that might prove each
    of the targets. Along the way, it computes hydras, i.e. collections of
    metavariables that occur in a collection of targets. For each such hydra
    it computes a list of paths to leaf nodes which pass through a target
    that makes use of at least one of the metavariables in the hydra. We call
    these heads of the hydra. Each must be cut off to prove the targets for
    that hydra. We then create a generator which will allow us to iterate over
    all the ways of killing all the heads of the current hydra. We then try to
    use unification to find a compatible set of assignments that will prove all
    the targets required to kill the current hydra. Along the way, new hydras
    may be created, and these are appended to the list if they aren't the same
    as a hydra we already dealt with. If all the original targets are proved
    at the end of this process, the function returns True, otherwise False.
    """
    dirty1 = []
    dirty2 = []
    plist = []
    hydras_done = []
    hydras_todo = []
    tarmv = target_metavars(screen, tl, ttree)
    d1, d2, pl = check_zero_metavar_unifications(screen, tl, ttree, tarmv)
    dirty1 += d1
    dirty2 += d2
    plist += pl
    unification_count, unifications = annotate_ttree(screen, tl, ttree, hydras_todo, tarmv)
    while hydras_todo:
        hydra = hydras_todo.pop()
        heads = find_hydra_heads(screen, tl, ttree, hydras_done, hydras_todo, hydra)
        gen = generate_pairs(heads, unification_count, len(heads))
        d1, d2, pl = try_unifications(screen, tl, ttree, unifications, gen)
        dirty1 += d1
        dirty2 += d2
        plist += pl
        hydras_done.append(hydra)
    for i in dirty1:
        screen.pad1.pad[i] = str(tl.tlist1.data[i])
    for i in dirty2:
        screen.pad2.pad[i] = str(tl.tlist2.data[i])
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()
    return all(t.proved for t in ttree.andlist) or ttree.proved, plist

def fill_macros(screen, tl):
    """
    Process macros. See corresponding function in logic module for details
    """
    logic.fill_macros(screen, tl)

    if len(tl.tlist0.data) > 0:  
        screen.pad0.pad[0] = str(tl.tlist0.data[0])
    for i in range(0, len(tl.tlist1.data)):
        screen.pad1.pad[i] = str(tl.tlist1.data[i])
    for i in range(0, len(tl.tlist2.data)):
        screen.pad2.pad[i] = str(tl.tlist2.data[i])
    screen.pad0.refresh()
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def select_substring(screen, tl):
    """
    Interface function for getting the user to select a substring of some
    hypothesis or target that an equality substitution is going to be applied
    to. The function returns a quadruple hyp, line, start, end. The value hyp
    is True if the selected substring is in a hypothesis, otherwise it is in
    a target. The index within the hypothesis/target pane is given by line.
    The start and end character indices are also returned, standing for the
    substring including the start index but not the end index.
    """
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
            if pad.scroll_line + pad.cursor_line < tlist.len() - 1:
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
            if line < tlist.len():
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
        elif c == 'KEY_UP' or c == 'KEY_DOWN' or c == '\t':
            continue
        else:
            pad.rev1 = 0
            pad.rev2 = 0
            pad.refresh()
            screen.status("")
            return True, 0, 0, 0 

def equality_substitution(screen, tl):
    """
    Gets the index of a hypothesis from the user which is an equality, and
    gets a substring of a hypothesis or target to apply it to and does the
    substitution. See the corresponding function in the logic module for
    details.
    """
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
    t = tlist1.data[line1]
    while isinstance(t, ForallNode):
        t = t.left
    if not isinstance(t, EqNode): # not an equality
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
    if not logic.equality_substitution(screen, tl, line1, line2, hyp2, sub_string, n):
        screen.dialog("Equality cannot be applied. Press Enter to continue")
        screen.restore_state()
        screen.focus.refresh()
        return
    else:
        sub_pad.pad[line2] = str(sub_tlist.data[line2])
        sub_pad.refresh()
    screen.restore_state()
    screen.focus.refresh()
    
def clear_tableau(screen, tl):
    """
    Clear the tableau and reset it ready to prove another theorem.
    """
    tlist0 = tl.tlist0
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    n1 = len(tlist1.data)
    n2 = len(tlist2.data)
    logic.clear_tableau(screen, tl)
    pad0 = screen.pad0
    pad1 = screen.pad1
    pad2 = screen.pad2
    pad0.pad[0] = ''
    for i in range(0, n1):
        pad1.pad[i] = ''
    for i in range(0, n2):
        pad2.pad[i] = ''
    pad0.scoll_line = 0
    pad0.cursor_line = 0
    pad0.scroll_char = 0
    pad0.cursor_char = 0
    pad1.scroll_line = 0
    pad1.cursor_line = 0
    pad1.scroll_char = 0
    pad1.cursor_char = 0
    pad2.scroll_line = 0
    pad2.cursor_line = 0
    pad2.scroll_char = 0
    pad2.cursor_char = 0
    pad2.refresh()
    pad1.refresh()
    pad0.refresh()
    screen.focus = screen.pad0

def library_import(screen, tl):
    """
    Read a theorem from the library to be added to the hypotheses of
    the current tableau. The function will first request a list of
    hashtags to filter by (which can be empty for no filtering) and
    will subsequently allow pressing a letter key to filter library
    results whose title begins with that letter (optional). Pressing
    Enter then loads the given result from the library into the tableau. 
    """
    tags = edit(screen, "Tags: ", 6, True)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with constraint shorthands
    taglist = tags_to_list(tags)
    library = open("library.dat", "r")
    filtered_titles = []
    title = library.readline()
    while title: # check for EOF
        library.readline() # skip constants for now
        library.readline() # skip terms for now
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
            if c == 'KEY_DOWN':
                if i < len(filtered_titles2) - 1:
                    i += 1
                    screen.status(filtered_titles2[i][1])
            elif c == 'KEY_UP':
                if i > 0:
                   i -= 1
                   screen.status(filtered_titles2[i][1])
            elif c.isalpha():
                filtered_titles2 = filter_titles(filtered_titles, c)
                i = 0
                if filtered_titles2:
                    screen.status(filtered_titles2[i][1])
                else:
                    screen.status("")
            elif c == '\n':
                if filtered_titles2:
                    screen.status('')
                    screen.focus.refresh()
                    break
            elif c == 'KEY_LEFT' or c == 'KEY_RIGHT' or c == '\t':
                continue
            else:
                library.close()
                screen.status('')
                screen.focus.refresh()
                return
        filepos = filtered_titles2[i][0]
        if logic.library_import(screen, tl, library, filepos):
            n = len(tl.tlist1.data) - 1
            screen.pad1.pad[n] = str(tl.tlist1.data[n])
            screen.pad1.refresh()
            screen.focus.refresh()
    library.close()

def library_load(screen, tl):
    """
    Load a tableau from the library to be proved. The function will
    first request a list of hashtags to filter by (which can be empty
    for no filtering) and will subsequently allow pressing a letter
    key to filter library results whose title begins with that letter
    (optional). Pressing Enter then loads the given result from the
    library into the tableau. 
    """
    tags = edit(screen, "Tags: ", 6, True)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with constraint shorthands
    taglist = tags_to_list(tags)
    library = open("library.dat", "r")
    filtered_titles = []
    title = library.readline()
    while title: # check for EOF
        library.readline() # skip constants for now
        library.readline() # skip terms for now
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
            if c == 'KEY_DOWN':
                if i < len(filtered_titles2) - 1:
                    i += 1
                    screen.status(filtered_titles2[i][1])
            elif c == 'KEY_UP':
                if i > 0:
                   i -= 1
                   screen.status(filtered_titles2[i][1])
            elif c.isalpha():
                filtered_titles2 = filter_titles(filtered_titles, c)
                i = 0
                if filtered_titles2:
                    screen.status(filtered_titles2[i][1])
                else:
                    screen.status("")
            elif c == '\n':
                if filtered_titles2:
                    screen.status('')
                    screen.focus.refresh()
                    break
            else:
                library.close()
                screen.status('')
                screen.focus.refresh()
                return
        filepos = filtered_titles2[i][0]
        tl.loaded_theorem = filepos
        dirty1, dirty2 = logic.library_load(screen, tl, library, filepos)
        screen.pad0.pad[0] = str(tl.tlist0.data[0])
        screen.pad0.refresh()
        for i in dirty1:
            screen.pad1.pad[i] = str(tl.tlist1.data[i])
        screen.pad1.refresh()
        for i in dirty2:
            screen.pad2.pad[i] = str(tl.tlist2.data[i])
        screen.pad2.refresh()
        screen.focus.refresh()
    library.close()

def library_export(screen, tl):
    """
    Write the current tableau out as a library result. This can only be done
    before manual mode or automation has been started, i.e. before creation
    of metavariables and skolemization and appending other information to the
    parse tree. The function will prompt to give a label for the theorem,
    which can be anything, and any hashtags to be specified for the theorem.
    """
    title = edit(screen, "Title: ", 7, True)
    if title == None:
        return
    tags = edit(screen, "Tags: ", 6, True)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with constraint shorthands
    library = open("library.dat", "a")
    logic.library_export(screen, tl, library, title, tags)
    library.close()
    screen.focus.refresh()

def select_hypothesis(screen, tl, second):
    """
    Allows the user to select a hypothesis, or if second is True, a target
    (after pressing TAB to switch panes). The function returns a tuple
    (forward, line) where forward is True if a hypothesis was selected,
    False if it was a target, and line is the line index in the relevant
    pane.
    """
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
            if pad.scroll_line + pad.cursor_line < tlist.len() - 1:
                pad.cursor_down()
                pad.refresh()
        elif c == 'KEY_RIGHT' or c == 'KEY_LEFT':
            continue
        elif second and c == '\t': # TAB = switch hypotheses/targets, forward/backward
            pad = screen.pad2 if forward else screen.pad1
            window = screen.win2 if forward else screen.win1
            tlist = tl.tlist2 if forward else tl.tlist1
            forward = not forward
            pad.refresh()
        elif c == '\x1b': # ESC = cancel
            return True, -1
        elif c == '\n':
            line = pad.scroll_line + pad.cursor_line
            if line < tlist.len():
                return forward, line
        elif c == 'KEY_RIGHT' or c == 'KEY_LEFT':
            continue
        else:
            return True, -1

""" Not needed at present
def negate_target(screen, tl):
    screen.save_state()
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    screen.status("Select target")
    forward, line = select_hypothesis(screen, tl, True)
    screen.status("")
    if line == -1: # Cancelled
        screen.status("")
        screen.restore_state()
        screen.focus.refresh()
        return
    if forward:
        screen.dialog("Not a target")
        screen.restore_state()
        screen.focus.refresh()
        return
    tree = tlist2.data[line]
    append_tree2(screen.pad1, tlist1.data, complement_tree(tree))
    tlist1.dep[len(tlist1.data) - 1] = line
    # update windows
    tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
    tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()
"""

def modus_ponens(screen, tl, ttree):
    """
    The modus ponens move, i.e. given P => Q and P, infers Q. The move accepts
    quantified implications and P can be a conjunction, in which the user will
    be prompted for multiple predicates to conjoin. The move can be applied for
    both forwards and backwards reasoning. P can also be matched against an
    implication S => T which will be interpreted as ¬S \wedge T.
    """
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
    t = tlist1.data[line1]
    while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
        t = t.left
    if not isinstance(t, ImpliesNode) and not isinstance(t, IffNode): # no implication after quantifiers
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
    line2_list = [line2]
    n = 1
    t = t.left if forward else t.right
    while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
        t = t.left
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
        line2_list.append(line2)
    # check everything is target compatible
    dep = tlist1.dependency(line1)
    for i in range(len(line2_list)):
        line2 = line2_list[i]
        dep = target_compatible(screen, tl, ttree, dep, line2, forward)
        if not dep:
            if len(line2_list) == 1:
                screen.dialog("Not target compatible. Press Enter to continue.")
            else:
                screen.dialog("Predicate "+str(i)+" not target compatible. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
    # run modus ponens
    success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, line2_list, forward)
    if not success:
        screen.dialog("Predicate does not match implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return # does not unify, bogus selection
    # update windows
    for i in dirty1:
        screen.pad1.pad[i] = str(tl.tlist1.data[i])
    for i in dirty2:
        screen.pad2.pad[i] = str(tl.tlist2.data[i])
    tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
    tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def modus_tollens(screen, tl, ttree):
    """
    The modus ponens move, i.e. given ¬Q => ¬P and P, infers Q. The move accepts
    quantified implications and P can be a conjunction, in which the user will
    be prompted for multiple predicates to conjoin. The move can be applied for
    both forwards and backwards reasoning. P can also be matched against an
    implication S => T which will be interpreted as ¬S \wedge T.
    """
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
    t = tlist1.data[line1]
    while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
        t = t.left
    if not isinstance(t, ImpliesNode) and not isinstance(t, IffNode): # no implication after quantifiers
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
    line2_list = [line2]
    n = 1
    t = t.left if forward else t.right
    t = complement_tree(t) # modus tollens unifies with complement
    while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
        t = t.left
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
        line2_list.append(line2)
    # check everything is target compatible
    dep = tlist1.dependency(line1)
    for i in range(len(line2_list)):
        line2 = line2_list[i]
        dep = target_compatible(screen, tl, ttree, dep, line2, forward)
        if not dep:
            if len(line2_list) == 1:
                screen.dialog("Not target compatible. Press Enter to continue.")
            else:
                screen.dialog("Predicate "+str(i)+" not target compatible. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
    # run modus tollens
    success, dirty1, dirty2 = logic.modus_tollens(screen, tl, ttree, dep, line1, line2_list, forward)
    if not success:
        screen.dialog("Predicate does not match implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return # does not unify, bogus selection
    # update windows
    for i in dirty1:
        screen.pad1.pad[i] = str(tl.tlist1.data[i])
    for i in dirty2:
        screen.pad2.pad[i] = str(tl.tlist2.data[i])
    tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
    tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def cleanup(screen, tl, ttree):
    """
    Apply automated cleanup moves. See the corresponding function in the logic
    module for details.
    """
    dirty1, dirty2 = logic.cleanup(screen, tl, ttree)
    
    screen.pad0[0] = str(tl.tlist0.data[0])
    for i in dirty1:
        screen.pad1.pad[i] = str(tl.tlist1.data[i])
    for i in dirty2:
        screen.pad2.pad[i] = str(tl.tlist2.data[i])
    
    screen.focus.cursor_adjust()
    screen.pad0.refresh()
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()
    return

def convert(screen, tl):
    """
    Reads every theorem/definition in the library and writes them back out
    to library2.dat. This is used to update the constant headers and to check
    that the library is in order.
    """
    library = open("library.dat", "r")
    library2 = open("library2.dat", "a")
    title = library.readline() # read title
    while title: # check for EOF
        consts = library.readline() # read constants
        terms = library.readline() # read terms
        tags = library.readline() # read tags
        filepos = library.tell()
        qz, tpred, impls = logic.fake_import(screen, tl, library, filepos)
        c0 = get_constants(screen, tl, qz) 
        c1 = get_constants(screen, tl, tpred)
        c2 = []
        for v in impls:
            if isinstance(v, ImpliesNode):
                c2.append((get_constants(screen, tl, v.left), get_constants(screen, tl, v.right)))
            elif isinstance(v, EqNode):
                c2.append(("=", get_constants(screen, tl, v.left), get_constants(screen, tl, v.right)))
            else:
                c2.append(get_constants(screen, tl, v))
        var = get_init_vars(screen, tl, qz) 
        d1 = get_terms(screen, tl, tpred, var)
        d2 = []
        for v in impls:
            if isinstance(v, ImpliesNode):
                d2.append((get_terms(screen, tl, v.left, var), get_terms(screen, tl, v.right, var)))
            else:
                d2.append(get_terms(screen, tl, v, var))
        const_str = "["+str(c0)+", "+str(c1)+", "+", ".join(str(v) for v in c2)+"]\n"
        terms_str = "["+str(d1)+", "+", ".join(str(v) for v in d2)+"]\n"
        library2.write(title)
        library2.write(const_str)
        library2.write(terms_str)
        library2.write(tags)
        library.seek(filepos)
        fstr = library.readline()
        while fstr != '\n':
            library2.write(fstr)
            fstr = library.readline()
        library2.write('\n')
        logic.clear_tableau(screen, tl)
        title = library.readline()
    library.close()
    library2.close()
