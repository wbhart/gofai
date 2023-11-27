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
from unification import unify, subst, trees_unify, is_predicate, sort_type_class, \
     is_function_type, sorts_compatible, coerce_sorts, sorts_equal, \
     check_macros, substitute
from utility import unquantify, relabel, relabel_constraints, append_tree, \
     append_tree2, replace_tree, replace_tree2, add_sibling, add_descendant, \
     skolemize_quantifiers, skolemize_statement, insert_sort, target_compatible, \
     target_depends, deps_defunct, deps_intersect, deps_compatible, \
     complement_tree, tags_to_list, canonicalise_tags, filter_titles, \
     trim_spaces, find_all, find_start_index, metavars_used, target_metavars, \
     domain, codomain, universe, system_unary_functions, \
     system_binary_functions, system_predicates, list_merge, get_constraint, \
     get_constants, merge_lists, process_constraints
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
                mark_proved(screen, tl, ttree, c)
                
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
                            mark_proved(screen, tl, ttree, j)
    check_contradictions(screen, tl, ttree, tarmv)
    for i in range(len(tlist2)):
        if isinstance(tlist2[i], EqNode):
            if not metavars_used(tlist2[i]):
                unifies, assign, macros = unify(screen, tl, tlist2[i].left, tlist2[i].right)
                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                if unifies:
                    mark_proved(screen, tl, ttree, i)
    
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
    hydras_done = []
    hydras_todo = []
    tarmv = target_metavars(screen, tl, ttree)
    check_zero_metavar_unifications(screen, tl, ttree, tarmv)
    unification_count, unifications = annotate_ttree(screen, tl, ttree, hydras_todo, tarmv)
    while hydras_todo:
        hydra = hydras_todo.pop()
        heads = find_hydra_heads(screen, tl, ttree, hydras_done, hydras_todo, hydra)
        gen = generate_pairs(heads, unification_count, len(heads))
        try_unifications(screen, tl, ttree, unifications, gen)
        hydras_done.append(hydra)
    return all(t.proved for t in ttree.andlist)

def mark_proved(screen, tl, ttree, n):
    """
    Given a target dependency tree, ttree, mark target n within this tree as
    proved, along with all the descendents of that node. Also set all
    hypotheses that can only be used to prove now proven nodes, to DeadNode
    (which shows up as a dashed line in the tableau) along with all the now
    proven nodes.
    """
    if ttree.num == n:
        if not ttree.proved:
            ttree.proved = True
            if n >= 0:
                screen.dialog("Target "+str(ttree.num)+" proved")
            for i in range(0, len(tl.tlist1.data)):
                if deps_defunct(screen, tl, ttree, n, i):
                    tl.tlist1.data[i] = DeadNode()
                    screen.pad1.pad[i] = str(tl.tlist1.data[i])
            screen.pad1.refresh()
            for i in range(0, len(tl.tlist2.data)):
                if target_depends(screen, tl, ttree, i, n): 
                    tl.tlist2.data[i] = DeadNode()
                    screen.pad2.pad[i] = str(tl.tlist2.data[i])
            screen.pad2.refresh()
            screen.focus.refresh()
        return True
    for P in ttree.andlist:
        if mark_proved(screen, tl, P, n):
            if all(t.proved for t in ttree.andlist) and not ttree.proved:
                ttree.proved = True
                if ttree.num >= 0:
                    screen.dialog("Target "+str(ttree.num)+" proved")
                for i in range(0, len(tl.tlist2.data)):
                    if deps_defunct(screen, tl, ttree, ttree.num, i):
                        tl.tlist1.data[i] = DeadNode()
                        screen.pad1.pad[i] = str(tl.tlist1.data[i])
                screen.pad1.refresh()
                for i in range(0, len(tl.tlist2.data)):
                    if target_depends(screen, tl, ttree, i, ttree.num): 
                        tl.tlist2.data[i] = DeadNode()
                        screen.pad2.pad[i] = str(tl.tlist2.data[i])
                screen.pad2.refresh()
                screen.focus.refresh()
            return True
    return False

def check_contradictions(screen, tl, ttree, tarmv):
    """
    Check for any contradictions amongst hypotheses that don't involve metavars
    in the list tarmv (taken to be a list of all metavars appearing in
    targets). Mark any targets proved for which the contradicting hypotheses
    are target compatible.
    """
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
                                mark_proved(screen, tl, ttree, t)

def element_universe(screen, x):
    """
    Function constraints specify a codomain rather than a universe. This
    function can be called to compute the appropriate universe for an element
    of the codomain (or indeed the domain, if required). One must be careful
    because the domain or codomain of a function may itself be expressed using
    some other constraint, e.g. a variable, function constraint, cartesian
    constraint, etc., and each case requires special handling.
    """
    if isinstance(x, VarNode):
        return x.sort.sort
    elif isinstance(x, FunctionConstraint):
        return x.sort # the type of a function constraint must be the type of a function
    elif isinstance(x, CartesianConstraint):
        return x.sort # ?? may need to take universes of components ??
    elif isinstance(x, SetOfNode):
        if isinstance(x.left, FunctionConstraint) or isinstance(x.left, CartesianConstraint):
            return x.left.sort
        else:
            return x.left
    else: # Universum, NumberSort, TupleSort are their own sorts
        return x

def propagate_sorts(screen, tl, tree0):
    """
    Given a parse tree where all variables have been annotated with their
    constraints, compute all the types for every node of the tree. The code
    to propagate types up the the tree from components of the current node
    comes first, followed by code to compute the types for the current node.
    """
    stree = tl.stree

    def propagate(tree):
        if tree == None:
            return True
        if isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
            ok = propagate(tree.var.constraint)
            if not ok:
                return False
            ok = propagate(tree.var)
            if not ok:
                return False
        if isinstance(tree, FnApplNode) or isinstance(tree, TupleNode):
            for v in tree.args:
                ok = propagate(v)
                if not ok:
                    return False
        if isinstance(tree, FnApplNode):
            ok = propagate(tree.var)
            if not ok:
                return False
        if isinstance(tree, FunctionConstraint):
            ok = propagate(tree.domain)
            if not ok:
                return False
            ok = propagate(tree.codomain)
            if not ok:
                return False
            if tree.domain:
                tree.sort = SetSort(TupleSort([element_universe(screen, tree.domain), element_universe(screen, tree.codomain)]))
            else:
                tree.sort = SetSort(TupleSort([None, element_universe(screen, tree.codomain)]))
        if isinstance(tree, CartesianConstraint):
            for v in tree.sorts:
                ok = propagate(v)
                if not ok:
                    return False
            tree.sort = TupleSort([s.sort for s in tree.sorts])
        if isinstance(tree, LRNode):
            if not propagate(tree.left):
                return False
            if not propagate(tree.right):
                return False
        if isinstance(tree, SetOfNode):
            tree.sort = SetSort(tree.left)
        if isinstance(tree, SymbolNode):
            propagate(tree.constraint)
            if tree.name() == "\\emptyset":
                 if isinstance(tree.constraint, VarNode):
                     tree.sort = SetSort(tree.constraint)
                 elif isinstance(tree.constraint, SetOfNode):
                     tree.sort = tree.constraint.sort
                 else:
                     tree.sort = SetSort(tree.constraint.sort)
        elif isinstance(tree, VarNode):
            if isinstance(tree.constraint, SetSort): # this variable is a set
                insert_sort(screen, tl, tree.constraint.sort, tree) # this set is a sort
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, PredSort): # this variable is a pred
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, FnApplNode): # check it is a universe of metavar
                if tree.constraint.name() != "universe":
                    screen.dialog(f"Variable {tree.name()} has invalid constraint")
                    # leave sort as None
                    return False
            elif isinstance(tree.constraint, VarNode): # check it is in a set
                if not isinstance(tree.constraint.constraint, SetSort):
                    screen.dialog(f"Variable {tree.name()} has invalid constraint")
                    return False
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, Universum): # variable is in universum
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, CartesianConstraint):
                propagate(tree.constraint)
                tree.sort = tree.constraint.sort
            elif isinstance(tree.constraint, FunctionConstraint):
                tree.sort = tree.constraint.sort
            elif isinstance(tree.constraint, NumberSort):
                tree.sort = tree.constraint
        elif isinstance(tree, TupleComponentNode):
            lsort = tree.left.sort
            if not isinstance(lsort, TupleSort):
                screen.dialog("Invalid tuple in component operation")
                return False
            idx = tree.right.value
            if idx < 0 or idx >= len(lsort.sorts):
                screen.dialog("Invalid tuple index")
                return False
            tree.sort = lsort.sorts[idx].sort
        elif isinstance(tree, CartesianNode):
            if not isinstance(tree.left.sort, SetSort) or \
               not isinstance(tree.right.sort, SetSort):
                screen.dialog("Cartesian product requires sets")
                return False
            tree.sort = SetSort(TupleSort([tree.left.sort.sort, tree.right.sort.sort]))
        elif isinstance(tree, NaturalNode):
            pass # dealt with by constructor
        elif isinstance(tree, ExpNode):
            if isinstance(tree.left.sort, Sort) and not isinstance(tree.left.sort, NumberSort):
                screen.dialog("Cannot raise {str(tree.left)} to power")
                return False
            elif not isinstance(sort_type_class(tree.left.sort), SemiringClass):
                    screen.dialog("Cannot raise {str(tree.left)} to power")
                    return False
            if not isinstance(tree.right.sort, NumberSort) or tree.right.sort.name() != "Natural":
                    screen.dialog("Powering operation not supported")
                    return False
            tree.sort = tree.left.sort
        elif isinstance(tree, CircNode):
            lsort = tree.left.sort
            rsort = tree.right.sort
            if not is_function_type(lsort) or \
               not is_function_type(rsort):    
                screen.dialog("Not a function in composition")
                return False
            if not sorts_equal(lsort.sort.sorts[0], rsort.sort.sorts[1]):
                screen.dialog("Type mismatch in function composition")
                return False
            tree.sort = SetSort(TupleSort([rsort.sort.sorts[0], lsort.sort.sorts[1]]))
        elif isinstance(tree, FnApplNode):
            if tree.name() in system_unary_functions or tree.name() in system_binary_functions:
                tree.sort = tree.args[0].sort
            elif tree.name() in system_predicates:
                tree.sort = PredSort()
            elif len(tree.args) == 0: # constant function
                fn_sort = tree.var.sort
                if fn_sort.sort.sort.sorts[0] != None:
                     screen.dialog(f"Wrong number of arguments to function {tree.name()}")
                     return False
                tree.sort = fn_sort.sort.sort.sorts[1]
            else:
                fn_sort = tree.var.sort
                if isinstance(fn_sort, PredSort):
                    if len(tree.args) != 1:
                        screen.dialog(f"Wrong number of arguments in predicate {tree.name()}")
                        return False
                    tree.sort = PredSort()
                else:
                    domain_sort = fn_sort.sort.sort.sorts[0]
                    codomain_sort = fn_sort.sort.sort.sorts[1]
                    if domain_sort == None:
                        screen.dialog(f"Wrong number of arguments to function {tree.name()}")
                        return False
                    if len(tree.args) == 1:
                        if not coerce_sorts(screen, tl, domain_sort, tree.args[0].sort):
                            screen.dialog(f"Type mismatch for argument {0} of {tree.name()}")
                            return False
                    else:
                        if len(tree.args) != len(domain_sort.sorts):
                            screen.dialog(f"Wrong number of arguments to function {tree.name()}")
                            return False
                        for i in range(len(tree.args)):
                            if not coerce_sorts(screen, tl, domain_sort.sorts[i], tree.args[i].sort):
                                screen.dialog(f"Type mismatch for argument {i} of {tree.name()}")
                                return False
                    tree.sort = codomain_sort
        elif isinstance(tree, LambdaNode):
            # can only be created by the system
            tree.sort = SetSort(TupleSort([tree.left.sort, tree.right.sort]))
        elif isinstance(tree, TupleNode):
            # will be used for all sorts of things, so no point checking anything
            tree.sort = TupleSort([v.sort for v in tree.args])
        elif isinstance(tree, PowerSetNode):
            if not isinstance(tree.left.sort, SetSort):
                screen.dialog("Argument to power set not a set")
                return False
            tree.sort = SetSort(tree.left.sort)
        elif isinstance(tree, AddNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                screen.dialog("Type mismatch in addition")
                return False
            if not isinstance(sort_type_class(tree.left.sort), MonoidClass):
                screen.dialog("Invalid type for addition")
                return False
            if not isinstance(sort_type_class(tree.right.sort), MonoidClass):
                screen.dialog("Invalid type for addition")
                return False
            tree.sort = tree.left.sort
        elif isinstance(tree, MulNode) or isinstance(tree, SubNode) or \
             isinstance(tree, DivNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                screen.dialog("Type mismatch in arithmetic operation")
                return False
            if not isinstance(sort_type_class(tree.left.sort), SemiringClass):
                screen.dialog("Invalid type for arithmetic operation")
                return False
            if not isinstance(sort_type_class(tree.right.sort), SemiringClass):
                screen.dialog("Invalid type for arithmetic operation")
                return False
            tree.sort = tree.left.sort
        elif isinstance(tree, LtNode) or isinstance(tree, GtNode) or \
             isinstance(tree, LeqNode) or isinstance(tree, GeqNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                screen.dialog("Type mismatch in order relation")
                return False
            if not isinstance(sort_type_class(tree.left.sort), PosetClass):
                screen.dialog("Invalid types for order relation")
                return False
            tree.sort = PredSort()
        elif isinstance(tree, EqNode) or isinstance(tree, NeqNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                screen.dialog("Type mismatch in equality relation")
                return False
            # many things can be assigned/compared equal, so can't restrict types
            tree.sort = PredSort()
        elif isinstance(tree, ImpliesNode) or isinstance(tree, IffNode) or \
             isinstance(tree, AndNode) or isinstance(tree, OrNode):
            if not isinstance(tree.left.sort, PredSort) or \
               not isinstance(tree.right.sort, PredSort):
                screen.dialog("Logical operator requires predicates")
                return False
            tree.sort = PredSort()
        elif isinstance(tree, IntersectNode) or isinstance(tree, UnionNode) or \
             isinstance(tree, DiffNode):
            lsort = tree.left.sort
            rsort = tree.right.sort
            if not isinstance(lsort, SetSort) or \
               not isinstance(rsort, SetSort):
                screen.dialog("Arguments to set operation are not sets")
                return False
            if not sorts_compatible(screen, tl, lsort.sort, rsort.sort):
                screen.dialog("Incompatible sets in set operation")
                return False
            tree.sort = lsort
        elif isinstance(tree, SubsetneqNode) or isinstance(tree, SubseteqNode) or \
             isinstance(tree, SupsetneqNode) or isinstance(tree, SupseteqNode):
            lsort = tree.left.sort
            rsort = tree.right.sort
            if not isinstance(lsort, SetSort) or \
               not isinstance(rsort, SetSort):
                screen.dialog("Arguments to set relation are not sets")
                return False
            if not sorts_compatible(screen, tl, lsort.sort, rsort.sort):
                screen.dialog("Incompatible sets in set relation")
                return False
            tree.sort = PredSort()
        elif isinstance(tree, SetBuilderNode):
            if not isinstance(tree.left.right.sort, SetSort):
                screen.dialog("Set comprehension must range over set")
                return False
            tree.sort = tree.left.right.sort
        elif isinstance(tree, AbsNode):
            if isinstance(tree.left.sort, SetSort):
                screen.dialog("Cannot take absolute value of set")
                return False
            if not isinstance(sort_type_class(tree.left.sort), ValuedFieldClass):
                screen.dialog("Incompatible argument type in absolute value")
                return False
            tree.sort = tree.left.sort
        elif isinstance(tree, NegNode):
            if isinstance(tree.left.sort, SetSort):
                screen.dialog("Cannot negate a set")
                return False
            if isinstance(tree.left.sort, PredSort):
                screen.dialog("Cannot negate a predicate")
                return False
            if not isinstance(sort_type_class(tree.left.sort), SemiringClass):
                screen.dialog("Invalid type for arithmetic operation")
                return False
            tree.sort = tree.left.sort
        elif isinstance(tree, NotNode):
            if not isinstance(tree.left.sort, PredSort):
                screen.dialog("Logical negation requires predicate")
                return False
            tree.sort = PredSort()
        elif isinstance(tree, BoolNode):
            tree.sort = PredSort()
        elif isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
            tree.sort = PredSort()
        elif isinstance(tree, ElemNode):
            if not isinstance(tree.right.sort, SetSort):
                screen.dialog("Not a set in element relation")
                return False
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort.sort, None, False):
                screen.dialog("Type mismatch in element relation")
                return False
            tree.sort = PredSort()
        elif isinstance(tree, SetSort):
            if tree.sort != tree:
                propagate(tree.sort)
        elif isinstance(tree, TupleSort):
            for i in range(len(tree.sorts)):
                propagate(tree.sorts[i])
        return True
    return propagate(tree0)

def process_sorts(screen, tl):
    """
    Every move, this function is called to recompute the types of nodes in any
    quantifier zone, hypothesis or target that hasn't previously been processed
    or which has been modified since last move. A record of the last binder in
    the quantifier zone, the last hypothesis and the last target already
    processed are stored in the tableau structure and these are reset if an
    already processed line is changed.
    """
    n0, n1, n2 = tl.sorts_processed
    i = 0
    if tl.tlist0.data:
        data = tl.tlist0.data[0]
        while i < n0:
            data = data.left # skip quantifiers we already typed
            i += 1
        if data:
            ok = propagate_sorts(screen, tl, data)
            if not ok:
                return False
            while data != None:
                data = data.left
                i += 1
    for j in range(n1, len(tl.tlist1.data)):
        ok = propagate_sorts(screen, tl, tl.tlist1.data[j])
        if not ok:
            return False
    for k in range(n2, len(tl.tlist2.data)):
        ok = propagate_sorts(screen, tl, tl.tlist2.data[k])
        if not ok:
            return False
    tl.sorts_processed = (i, len(tl.tlist1.data), len(tl.tlist2.data))
    return True

def type_vars(screen, tl):
    """
    When beginning to prove a theorem, the initial tableau needs each variable
    annotated with its constraints as defined by its corresponding binder. This
    function is called once manual or automated mode is started to do this
    annotation.
    """
    constraints = dict() # all constraints of all vars
    vars = [] # vars currently in scope

    if len(tl.tlist0.data) > 0:
        qz = tl.tlist0.data[0]
    else:
        qz = None

    i = 0
    while qz != None:
        vars.append(qz.var.name())
        constraints[qz.var.name()] = qz.var.constraint
        ok = process_constraints(screen, qz.var.constraint, constraints, vars)
        if not ok:
            return
        qz = qz.left
        i += 1

    hyps = tl.tlist1.data
    for tree in hyps:
        ok = process_constraints(screen, tree, constraints, vars)
        if not ok:
            return
    tars = tl.tlist2.data
    for tree in tars:
        ok = process_constraints(screen, tree, constraints, vars)
        if not ok:
            return
    tl.constraints = constraints
    tl.constraints_processed = (i, len(tl.tlist1.data), len(tl.tlist2.data))

def update_constraints(screen, tl):
    """
    After every move, additional variables could have been added to the
    quantifier zone, or additional hypotheses or targets could have been
    added to the tableau. In such cases, this function can be called to
    annotate all variables that appear in them with their constraints.
    A count of the number of already processed binders in the quantifier
    zone, hypotheses and targets is stored in the tableau structure. This
    can be reset if a change is made to one of the already processed
    lines of the tableau.
    """
    n0, n1, n2 = tl.constraints_processed
    constraints = tl.constraints

    if len(tl.tlist0.data) > 0:
        qz = tl.tlist0.data[0]
    else:
        qz = None

    i = 0
    while i < n0: # skip already processed quantifiers
        qz = qz.left
        i += 1

    while qz != None:
        constraints[qz.var.name()] = qz.var.constraint
        ok = process_constraints(screen, qz.var.constraint, constraints)
        if not ok:
            return False
        qz = qz.left
        i += 1

    hyps = tl.tlist1.data
    for j in range(n1, len(hyps)):
        ok = process_constraints(screen, hyps[j], constraints)
        if not ok:
            return False
    tars = tl.tlist2.data
    for k in range(n2, len(tars)):
        ok = process_constraints(screen, tars[k], constraints)
        if not ok:
            return False
    tl.constraints_processed = (i, len(hyps), len(tars))
    return True
        
def fill_macros(screen, tl):
    """
    When the tableau is initiall loaded, before any processing whatsoever,
    there may be macros in the tableau (universe, domain, codomain, etc.)
    which need to be computed. This function also needs to be called every
    move as it is possible that some inference filled in a metavariable,
    at which point a macro with that variable as parameter may now be
    computed. Generally, this function must be called before any processing
    of constraints or sorts. The only macros that can't be filled in are
    those whose parameter is a metavariable about which the required
    information is not known. This happens for example when theorems are
    loaded from the library, before they are instantiated.
    """
    def fill(tree, data):
        if tree == None:
            return None
        if isinstance(tree, FnApplNode):
            if tree.name() == 'universe':
                return SetOfNode(universe(tree.args[0], data))
            if tree.name() == 'domain':
                return domain(tree.args[0], data)
            if tree.name() == 'codomain':
                return codomain(tree.args[0], data)
            for i in range(0, len(tree.args)):
                tree.args[i] = fill(tree.args[i], data)
            return tree
        elif isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            tree.var.constraint = fill(tree.var.constraint, data)
            new_data = deepcopy(tree)
            new_data.left = data
            tree.left = fill(tree.left, new_data)
            return tree
        elif isinstance(tree, TupleNode):
            for i in range(0, len(tree.args)):
                tree.args[i] = fill(tree.args[i], data)
            return tree
        elif isinstance(tree, LRNode):
            tree.left = fill(tree.left, data)
            tree.right = fill(tree.right, data)
            return tree
        elif isinstance(tree, SymbolNode):
            tree.constraint = fill(tree.constraint, data)
            return tree
        elif isinstance(tree, LeafNode):
            return tree
        else:
            return tree

    data = tl.tlist0.data[0] if tl.tlist0.data else []
    if len(tl.tlist0.data) > 0:
        tl.tlist0.data[0] = fill(tl.tlist0.data[0], data)
        screen.pad0.pad[0] = str(tl.tlist0.data[0])
    for i in range(0, len(tl.tlist1.data)):
        tl.tlist1.data[i] = fill(tl.tlist1.data[i], data)
        screen.pad1.pad[i] = str(tl.tlist1.data[i])
    for i in range(0, len(tl.tlist2.data)):
        tl.tlist2.data[i] = fill(tl.tlist2.data[i], data)
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
    c0 = get_constants(screen, tl, tl.tlist0.data[0]) 
    c1 = merge_lists([get_constants(screen, tl, v) for v in tl.tlist1.data])
    c2 = merge_lists([get_constants(screen, tl, v) for v in tl.tlist2.data])
    consts = "["+str(c0)+", "+str(c1)+", "+str(c2)+"]"        
    library = open("library.dat", "a")
    library.write(title+"\n")
    library.write(consts+"\n")
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
    Automated cleanup moves. This applies numerous moves that the user will
    essentially always want to do. This is applied automatically after every
    move to make less work for the user. The moves applied are the following:
      * skolemization of existentially bound variables
      * creation of metavariables
      * moving outside binders on hypotheses/targets to the quantifier zone
    For hypotheses we perform the following moves:
      * convert P \vee P to P
      * convert ¬P \vee Q to P => Q
      * convert P \iff Q to P => Q and Q => P
      * replace P \wedge P with P
      * convert P \wedge Q to P and Q
      * convert ¬(P \implies Q) to P and ¬Q
      * convert (P \vee Q) => R to P => R and Q => R if such implications
        would not introduce new metavariables
      * convert P => (Q \wedge R) to P => Q and P => R
    For targets we perform the following moves:
      * for P \vee Q introduce a hypothesis ¬P and replace the implication with Q,
        with appropriate dependency tracking
      * for P => Q introduce a hypothesis P and replace the implication with Q, with
        appropriate dependency tracking
      * convert P \wedge P to P
      * convert P \wedge Q to P and Q
      * convert ¬(P \implies Q) to P and ¬Q
    These are applied repeatedly until no further automated moves are possible.
    """
    tl0 = tl.tlist0.data # quantifier zone
    tl1 = tl.tlist1.data # hypotheses
    tl2 = tl.tlist2.data # targets
    deps = []
    sk = []
    qz = []
    mv = []
    if tl0:
        sq, deps, sk, ex = skolemize_quantifiers(tl0[0], deps, sk, [])
        qzext = []
        if len(ex) > 0: # constraint of new skolem variable will need to be recomputed
           tl.constraints_processed = (0, 0, 0)
           tl.sorts_processed = (0, 0, 0)
        for i in range(len(ex)):
            n = sk[i][1] # number of dependencies
            domain_constraints = [v.var.constraint if isinstance(v, ForallNode) else v.constraint for v in deps[0:n]]
            if len(domain_constraints) > 1:
                fn_constraint = FunctionConstraint(DomainTuple(domain_constraints), SetOfNode(ex[i].constraint))
            elif len(domain_constraints) == 1:
                fn_constraint = FunctionConstraint(domain_constraints[0], SetOfNode(ex[i].constraint))
            else:
                fn_constraint = FunctionConstraint(None, SetOfNode(ex[i].constraint))
            var = VarNode(ex[i].name(), fn_constraint)
            var.skolemized = True # make sure we don't skolemize it again
            qzext.append(ExistsNode(var, None))
        if qzext:
            root = qzext[0]
            t = root
            t.left = None
            for i in range(1, len(qzext)):
                v = qzext[i]
                v.left = None
                t.left = v
                t = t.left
            if sq:
                t.left = sq
            tl.tlist0.data[0] = root
        else:
            tl.tlist0.data[0] = sq
        screen.pad0[0] = str(tl.tlist0.data[0])
        
    d = len(deps)
    s = len(sk)
    m = len(mv)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()
    
    depmin = d # avoid dependencies on original qz variables

    if tl0: # process constraints of variables in qz
        tree = tl0[0]
        while tree:
            tree.var.constraint = skolemize_statement(screen, tree.var.constraint, deps, depmin, sk, qz, mv, True, False)
            rollback()
            tree = tree.left

    hyps_done = False
    tars_done = False
    i = 0
    j = 0
    while not hyps_done or not tars_done:
        if not hyps_done:
            hyps_done = True
            while i < len(tl1):
                tl1[i] = skolemize_statement(screen, tl1[i], deps, depmin, sk, qz, mv, False, False)
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
                    unifies, assign, macros = unify(screen, tl, tl1[i].left, tl1[i].right)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if unifies and not assign:
                        replace_tree2(screen.pad1, tl1, i, tl1[i].left)
                    else:
                        stmt = ImpliesNode(complement_tree(tl1[i].left), tl1[i].right)
                        if isinstance(stmt.left, NotNode) and isinstance(stmt.right, NotNode):
                            temp = stmt.left.left
                            stmt.left = stmt.right.left
                            stmt.right = temp
                        replace_tree2(screen.pad1, tl1, i, stmt)
                if isinstance(tl1[i], IffNode):
                    tl1[i] = ImpliesNode(tl1[i].left, tl1[i].right)
                    impl = ImpliesNode(deepcopy(tl1[i].right), deepcopy(tl1[i].left))
                    append_tree2(screen.pad1, tl1, impl)
                    tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                    stmt = skolemize_statement(screen, tl1[i], deps, depmin, sk, qz, mv, False)
                    replace_tree2(screen.pad1, tl1, i, stmt)
                    rollback()
                while isinstance(tl1[i], AndNode):
                    # First check we don't have P \wedge P
                    unifies, assign, macros = unify(screen, tl, tl1[i].left, tl1[i].right)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if unifies and not assign:
                        replace_tree2(screen.pad1, tl1, i, tl1[i].left)
                    else:
                        append_tree2(screen.pad1, tl1, tl1[i].right)
                        replace_tree2(screen.pad1, tl1, i, tl1[i].left)
                        tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                if isinstance(tl1[i], NotNode) and isinstance(tl1[i].left, ImpliesNode):
                    append_tree2(screen.pad1, tl1, complement_tree(tl1[i].left.right))
                    replace_tree2(screen.pad1, tl1, i, tl1[i].left.left)
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
                        append_tree2(screen.pad1, tl1, ImpliesNode(Q, R))
                        replace_tree2(screen.pad1, tl1, i, ImpliesNode(P, R))
                        tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                if isinstance(tl1[i], ImpliesNode) and isinstance(tl1[i].right, AndNode):
                    stmt = ImpliesNode(deepcopy(tl1[i].left), tl1[i].right.left)
                    append_tree2(screen.pad1, tl1, stmt)
                    stmt = ImpliesNode(tl1[i].left, tl1[i].right.right)
                    replace_tree2(screen.pad1, tl1, i, stmt)
                    tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                screen.pad1[i] = str(tl1[i])
                i += 1
                while len(mv) > m:
                    mv.pop()
        if not tars_done:
            tars_done = True
            while j < len(tl2):
                tl2[j] = skolemize_statement(screen, tl2[j], deps, depmin, sk, qz, mv, True)
                rollback()
                if isinstance(tl2[j], OrNode):
                    append_tree2(screen.pad1, tl1, complement_tree(tl2[j].left))
                    hyps_done = False
                    replace_tree2(screen.pad2, tl2, j, tl2[j].right)
                    tl.tlist1.dep[len(tl1) - 1] = [j]
                if isinstance(tl2[j], ImpliesNode):
                    # can't relabel or metavar dependencies between existing targets broken
                    # left = relabel(screen, tl, [], tl2[j].left, tl.vars, True)
                    left = tl2[j].left
                    append_tree2(screen.pad1, tl1, left)
                    hyps_done = False
                    # can't relabel or metavar dependencies between existing targets broken
                    # right = relabel(screen, tl, [], tl2[j].right, tl.vars, True)
                    right = tl2[j].right
                    replace_tree2(screen.pad2, tl2, j, right)
                    tl.tlist1.dep[len(tl1) - 1] = [j]
                while isinstance(tl2[j], AndNode):
                    # First check we don't have P \wedge P
                    unifies, assign, macros = unify(screen, tl, tl2[j].left, tl2[j].right)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if unifies and not assign:
                        replace_tree2(screen.pad1, tl2, j, tl2[j].left)
                    else:
                        append_tree2(screen.pad2, tl2, tl2[j].right)
                        replace_tree2(screen.pad2, tl2, j, tl2[j].left)
                        add_sibling(screen, tl, ttree, j, len(tl2) - 1)
                if isinstance(tl2[j], NotNode) and isinstance(tl2[j].left, ImpliesNode):
                    append_tree2(screen.pad2, tl2, complement_tree(tl2[j].left.right))
                    replace_tree2(screen.pad2, tl2, j, tl2[j].left.left)
                    add_sibling(screen, tl, ttree, j, len(tl2) - 1)
                screen.pad2[j] = str(tl2[j])
                if not isinstance(tl2[j], ForallNode) and not isinstance(tl2[j], ExistsNode) \
                   and not isinstance(tl2[j], ImpliesNode):
                    j += 1
                while len(mv) > m:
                    mv.pop()
    
    if qz:
        tl.constraints_processed = (0, 0, 0)
        tl.sorts_processed = (0, 0, 0)
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
    return

#def convert(screen, tl):
#    library = open("library.dat", "r")
#    library2 = open("library2.dat", "a")
#    title = library.readline() # read title
#    while title: # check for EOF
#        tags = library.readline() # read tags
#        filepos = library.tell()
#        logic.library_load(screen, tl, library, filepos)
#        c0 = get_constants(screen, tl, tl.tlist0.data[0]) 
#        c1 = merge_lists([get_constants(screen, tl, v) for v in tl.tlist1.data])
#        c2 = merge_lists([get_constants(screen, tl, v) for v in tl.tlist2.data])
#        const_str = "["+str(c0)+", "+str(c1)+", "+str(c2)+"]\n"
#        library2.write(title)
#        library2.write(const_str)
#        library2.write(tags)
#        library.seek(filepos)
#        fstr = library.readline()
#        while fstr != '\n':
#            library2.write(fstr)
#            fstr = library.readline()
#        library2.write('\n')
#        logic.clear_tableau(screen, tl)
#        title = library.readline()
#    library.close()
#    library2.close()
