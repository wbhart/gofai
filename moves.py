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
     SortNode, find_sort, insert_sort

from editor import edit
from parser import to_ast
from interface import nchars_to_chars
from heapq import merge

system_unary_functions = ['complement', 'universe']
system_binary_functions = ['min', 'max']
system_predicates = ['is_bounded', 'is_upper_bound', 'is_lower_bound', 'is_supremum', 'is_infimum', 'is_pair', 'is_function', 'is_injective', 'is_surjective', 'is_bijective']

class TargetNode:
    def __init__(self, num, andlist=[]):
        self.num = num # which target this node corresponds to
        self.proved = False # start in unproved state
        self.andlist = andlist # a list of targets that would prove this target
        self.metavars = [] # metavariables used by this target
        self.unifies = [] # list of hyps this target unifies with on its own

    def __str__(self):
        if not self.andlist:
            return "("+str(self.num)+")"
        else:
            return "("+str(self.num)+", ["+", ".join([str(j) for j in self.andlist])+"])"

def is_ground(tree): # an expression is ground if it contains no metavars
    if tree == None:
        return True
    elif isinstance(tree, LRNode):
        if not is_ground(tree.left):
            return False 
        return search(tree.right)
    elif isinstance(tree, VarNode):
        return not tree.is_metavar
    elif isinstance(tree, FnApplNode):
        if tree.is_metavar:
            return False
        for v in tree.args:
            if not is_ground(v):
                return False
    elif isinstance(tree, TupleNode):
        for v in tree.args:
            if not is_ground(v):
                return False
    return True

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
                name = tree.name()
                if name not in used:
                    used.append(name)
        elif isinstance(tree, FnApplNode):
            if tree.is_metavar:
                name = tree.name()
                if name not in used:
                    used.append(name)
            for v in tree.args:
                search(v)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                search(v)
        
    search(tree)
    return used

def list_merge(list1, list2):
    r = []
    L = merge(list1, list2)
    v = ''
    for var in L:
        if var != v:
           r.append(var)
        v = var
    return r

def target_metavars(screen, tl, ttree):
    target_metavars = []
    tlist2 = tl.tlist2.data
    
    def mvars(ttree, target_metavars):
        if ttree.proved:
            return target_metavars
        if ttree.num != -1:
            ttree.metavars = metavars_used(tlist2[ttree.num])
            ttree.metavars.sort()
            target_metavars = list_merge(target_metavars, ttree.metavars)
        for t in ttree.andlist:
            target_metavars = mvars(t, target_metavars)
        return target_metavars

    return mvars(ttree, target_metavars)

def annotate_ttree(screen, tl, ttree, hydras, tarmv):
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

def find_start_index(lst, chosen_set):
    index = len(lst)
    for i in reversed(range(len(lst))):
        if lst[i] in chosen_set:
            break
        index = i
    return index

def generate_pairs(V, L, r, i=0, last_chosen_c=None):
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
                for rest in generate_pairs(V, L, r, i+1, last_chosen_c):
                    yield [(c, d)] + rest
            last_chosen_c.remove(c)

def find_hydra_heads(screen, tl, ttree, hydras_done, hydras_todo, hydra):
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

def initialise_sorts(screen, tl):
    stree = SortNode(Universum())
    tl.stree = stree 
    C = NumberSort("\\mathbb{C}", CompleteValuedFieldClass())
    R = NumberSort("\\mathbb{R}", CompleteOrderedValuedFieldClass())
    Q = NumberSort("\\mathbb{Q}", FieldClass())
    Z = NumberSort("\\mathbb{Z}", OrderedRingClass())
    N = NumberSort("\\mathbb{N}", OrderedSemiringClass())
    insert_sort(screen, tl, Universum(), C)
    insert_sort(screen, tl, C, R)
    insert_sort(screen, tl, R, Q)
    insert_sort(screen, tl, Q, Z)
    insert_sort(screen, tl, Z, N)   

def element_universe(x):
    if isinstance(x, VarNode):
        return x.sort.sort
    elif isinstance(x, FunctionConstraint):
        return x.sort # the type of a function constraint must be the type of a function
    elif isinstance(x, CartesianConstraint):
        return x.sort # ?? may need to take universes of components ??
    elif isinstance(x, SetOfNode):
        return x.left
    else: # Universum, NumberSort, TupleSort are their own sorts
        return x

def propagate_sorts(screen, tl, tree0):
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
                tree.sort = SetSort(TupleSort([element_universe(tree.domain), element_universe(tree.codomain)]))
            else:
                tree.sort = SetSort(TupleSort([None, element_universe(tree.codomain)]))
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
        #if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
        #    if not propagate(tree.var.constraint):
        #        return False
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
            #elif isinstance(tree.constraint, TupleSort):
            #    tree.sort = tree.constraint
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
            if not sorts_equal(lsort.sort.sorts[1], rsort.sort.sorts[0]):
                screen.dialog("Type mismatch in function composition")
                return False
            tree.sort = SetSort(TupleSort([lsort.sort.sorts[0], rsort.sort.sorts[1]]))
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
        #elif isinstance(tree, CartesianNode):
        #    lsort = tree.left.sort
        #    rsort = tree.right.sort
        #    if not isinstance(lsort, SetSort) or \
        #       not isinstance(rsort, SetSort):
        #        screen.dialog("Arguments to cartesian product are not sets")
        #        return False
        #    tree.sort = SetSort(TupleSort([lsort.sort, rsort.sort]))
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
    
def get_constraint(var, qz):
    tree = qz
    name = var.name()
    while qz:
        if qz.var.name() == name:
            return qz.var.constraint
        qz = qz.left
    raise Exception("Binder not found for "+var.name())

def process_constraints(screen, tree, constraints, vars=None):
    def del_last(L, str):
        gen = (len(L) - 1 - i for i, v in enumerate(reversed(L)) if v == str)
        del L[next(gen, None)]

    if isinstance(tree, ForallNode) \
         or isinstance(tree, ExistsNode):
        name = tree.var.name()
        if vars != None:
            vars.append(name)
        constraints[tree.var.name()] = tree.var.constraint
        ok = process_constraints(screen, tree.var.constraint, constraints, vars)
        if not ok:
            return False
        ok = process_constraints(screen, tree.left, constraints, vars)
        if vars != None:
            del_last(vars, name)
        if not ok:
            return False
    elif isinstance(tree, SetBuilderNode):
        name = tree.left.left.name()
        if vars != None:
            vars.append(name)
        constraints[tree.left.left.name()] = tree.left.left.constraint
        ok = process_constraints(screen, tree.left, constraints, vars)
        if not ok:
            if vars != None:
                del_last(vars, name)
            return False
        ok = process_constraints(screen, tree.right, constraints, vars)
        if vars != None:
            del_last(vars, name)
        if not ok:
            return False
    elif isinstance(tree, VarNode):
        varnames = vars if vars != None else constraints
        if not tree.name() in varnames:
            if tree.name() not in system_unary_functions and \
               tree.name() not in system_binary_functions and \
               tree.name() not in system_predicates:
               screen.dialog(f"Unknown variable/function {tree.name()}")
               return False
        else:
            tree.constraint = constraints[tree.name()]
    elif isinstance(tree, LRNode):
        ok = process_constraints(screen, tree.left, constraints, vars)
        if not ok:
            return False
        ok = process_constraints(screen, tree.right, constraints, vars)
        if not ok:
            return False
    elif isinstance(tree, FnApplNode):
        ok = process_constraints(screen, tree.var, constraints, vars)
        if not ok:
            return False
        for v in tree.args:
            ok = process_constraints(screen, v, constraints, vars)
            if not ok:
                return False
    elif isinstance(tree, TupleNode):
        for v in tree.args:
            ok = process_constraints(screen, v, constraints, vars)
            if not ok:
                return False
    elif isinstance(tree, SymbolNode):
         ok = process_constraints(screen, tree.constraint, constraints, vars)
         if not ok:
             return False
    return True

def type_vars(screen, tl):
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

def universe(tree, qz):
    if isinstance(tree, VarNode):
        t = get_constraint(tree, qz)
        return t.sort
    elif isinstance(tree, UnionNode) or isinstance(tree, IntersectNode) or \
         isinstance(tree, DiffNode):
        return universe(tree.left, qz)
    elif isinstance(tree, CartesianNode):
        return TupleSort([universe(tree.left, qz), universe(tree.right, qz)])
    elif isinstance(tree, FnApplNode) and tree.name() == 'complement':
        return universe(tree.args[0], qz)
    elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset':
        return tree.constraint
    else:
        return None # no universe

def domain(tree, qz):
    if isinstance(tree, VarNode):
        if tree.is_metavar:
            return None
        else:
            fn_constraint = get_constraint(tree, qz)
            return fn_constraint.domain
    else:
        return None # no domain

def codomain(tree, qz):
    if isinstance(tree, VarNode):
        if tree.is_metavar:
            return None
        else:
            fn_constraint = get_constraint(tree, qz)
            return fn_constraint.codomain
    else:
        return None # no domain
        
def fill_macros(screen, tl):
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

def check_macros(screen, tl, macros, assign, qz):
    qz = qz[0] if len(qz) > 0 else []
    # check macros after substitution
    for (uni1, tree2) in macros:
        tree = substitute(deepcopy(tree2.args[0]), assign)
        if tree2.name() == 'universe':
            tree = universe(tree, qz)
        elif tree2.name() == 'domain':
            tree = domain(tree, qz)
        elif tree2.name() == 'codomain':
            tree = codomain(tree, qz)
        if tree == None:
            return False
        unified, assign, macr = unify(screen, tl, uni1, tree, assign)
        macros.extend(macr)
        if not unified:
            return False
    return True

def mark_proved(screen, tl, ttree, n):
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

def deps_compatible(screen, tl, ttree, i, j):
    dep_list = tl.tlist1.dependency(j) # targets provable by hypothesis j
    if -1 in dep_list: # hyp j can prove anything
        return True

    def find(ttree, i):
        if ttree.num == i:
            return ttree
        for P in ttree.andlist:
            t = find(P, i)
            if t:
                return t
        return None

    for d in dep_list:
        root = find(ttree, d) # find target d
        if find(root, i): # target i is a descendent of d
            return True
    return False

def deps_intersect(screen, tl, ttree, i, j):
    deps_i = tl.tlist1.dependency(i) # targets provable by hyp i
    deps_j = tl.tlist1.dependency(j) # targets provable by hyp j
    if -1 in deps_i:
         return deps_j
    if -1 in deps_j:
         return deps_i
    deps = []
    for d1 in deps_j:
        for d2 in deps_i:
            if d1 < d2:
                d1, d2 = d2, d1
            if target_depends(screen, tl, ttree, d1, d2):
                if d1 not in deps:
                    deps.append(d1)
    return deps

def deps_defunct(screen, tl, ttree, i, j):
    deps_j = tl.tlist1.dependency(j) # targets provable by hyp j
    if -1 in deps_j: # hyp j can prove everything, can't be made defunct
        return False

    def find(ttree, i):
        if ttree.num == i:
            return ttree
        for P in ttree.andlist:
            t = find(P, i)
            if t:
                return t
        return None

    root = find(ttree, i)
    for d in deps_j:
        if not find(root, d): # we can't prove d from i
            return False
    return True

def target_depends(screen, tl, ttree, i, j):
     def find(ttree, i):
        if ttree.num == i:
            return ttree
        for P in ttree.andlist:
            t = find(P, i)
            if t:
                return t
        return None

     root = find(ttree, j) # find target j
     if find(root, i): # i is a descendent of j
         return True
     return False

def check_contradictions(screen, tl, ttree, tarmv):
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
                
def relabel_varname(name, var_dict):
    sp = name.split("_")
    if sp.pop().isdigit():
        name = '_'.join(sp)
    if name in var_dict:
        subscript = var_dict[name] + 1
    else:
        subscript = 0
    var_dict[name] = subscript
    return name+'_'+str(subscript)

def qz_copy_var(screen, tl, extras, name, new_name):
    node_to_copy = None
    qz = tl.tlist0.data[0]
    tree = qz

    for v in extras: # extra variables to rename, from unquantify
       if isinstance(v, ExistsNode) or isinstance(v, ForallNode):
          if v.var.name() == name: # found the relevant variable
              node_to_copy = v

    while tree != None:
       if isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
          if tree.var.name() == new_name:
              return
          if tree.var.name() == name: # found the relevant variable
              node_to_copy = tree
       if tree.left == None and node_to_copy != None: # this is the last node, make copy
          new_node = copy(node_to_copy)
          new_node.var = deepcopy(new_node.var)
          if isinstance(new_node.var, VarNode):
              new_node.var._name = new_name # rename
          elif isinstance(new_node.var, FnApplNode):
              new_node.var.var._name = new_name # rename
          new_node.left = None
          tree.left = new_node   
       tree = tree.left
    screen.pad0.pad[0] = str(qz)
    screen.pad0.refresh()
    screen.focus.refresh()
       
def relabel(screen, tl, extras, tree, tldict, update_qz=False):
    # update_qz makes a copy of variable in QZ with new name, if set
    vars_dict = dict()
    
    def process(tree, constraint=False):
        if tree == None:
            return
        if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            name = tree.var.name()
            new_name = relabel_varname(name, tldict)
            vars_dict[name] = new_name
            process(tree.var, constraint)
            process(tree.left, constraint)
            #process(tree.var.constraint, True) # seems to duplicate constraint proc below
        elif isinstance(tree, VarNode):
            process(tree.constraint, True)
            name = tree.name()
            if name in vars_dict:
                new_name = vars_dict[name]
                tree._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name)
            elif not constraint and tree.is_metavar:
                new_name = relabel_varname(name, tldict)
                vars_dict[name] = new_name
                tree._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name)
        elif isinstance(tree, SetBuilderNode):
            name = tree.left.left.name()
            new_name = relabel_varname(name, tldict)
            vars_dict[name] = new_name
            process(tree.left, constraint)
            process(tree.right, constraint)
        elif isinstance(tree, LRNode):
            process(tree.left, constraint)
            process(tree.right, constraint)
        elif isinstance(tree, FnApplNode):
            name = tree.name()
            if isinstance(tree.var, VarNode) and name in vars_dict:
                new_name = vars_dict[name] # TODO : add setter for assignment
                tree.var._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name)
            elif tree.is_metavar:
                new_name = relabel_varname(name, tldict)
                vars_dict[name] = new_name
                tree.var._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name)
            else:
                process(tree.var, constraint)
            #######
            for v in tree.args:
                process(v, constraint)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                process(v, constraint)
        elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset':
            process(tree.constraint, constraint)
        elif isinstance(tree, SetSort):
            process(tree.sort, constraint)
        elif isinstance(tree, TupleSort):
            for v in tree.sorts:
                process(v, constraint)
        elif isinstance(tree, FunctionConstraint):
            process(tree.domain, constraint)
            process(tree.codomain, constraint)
        elif isinstance(tree, CartesianConstraint):
            for v in tree.sorts:
                process(v, constraint)
    t = tree
    while isinstance(t, ForallNode) or isinstance(t, ExistsNode):
        name = t.var.name()
        new_name = relabel_varname(name, tldict)
        vars_dict[name] = new_name
        t.var._name = new_name # TODO : allow assignment of name for FnApplNode
        process(t.var.constraint)
        t = t.left

    process(t)
    return tree

def relabel_constraints(screen, tl, tree):
    vars_dict = dict()
    tldict = tl.vars # current subscripts

    def process(tree):
        if tree == None:
            return
        if isinstance(tree, Universum):
            name = tree.name()
            if name == '\\mathcal{U}':
                if name in vars_dict:
                    tree._name = vars_dict[name]
                else:
                    new_name = relabel_varname(name, tldict)
                    vars_dict[name] = new_name
                    tree._name = new_name
                    s = SortNode(tree) # insert new sort for new metavar universum
                    s.subsorts.append(tl.stree)
                    tl.stree = s
        if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            process(tree.var.constraint)
            process(tree.left)
        elif isinstance(tree, VarNode):
            process(tree.constraint)
        elif isinstance(tree, SetBuilderNode):
            process(tree.left)
            process(tree.right)
        elif isinstance(tree, LRNode):
            process(tree.left)
            process(tree.right)
        elif isinstance(tree, FnApplNode):
            process(tree.var)
            for v in tree.args:
                process(v)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                process(v)
        elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset' and \
                      isinstance(tree.sort, VarNode):
            process(tree.sort)
        elif isinstance(tree, SetSort):
            process(tree.sort)
        elif isinstance(tree, FunctionConstraint):
            process(tree.domain)
            process(tree.codomain)
        elif isinstance(tree, CartesianConstraint):
            for v in tree.sorts:
                process(v)
        elif isinstance(tree, DomainTuple):
            for v in tree.sets:
                process(v)
            for v in tree.sort.sets:
                process(v)

    process(tree)
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

def apply_equality(screen, tl, tree, string, n, subst, occurred=-1):
    occur = occurred
    found = False
    if tree == None:
        return False, None, occur
    if str(tree) == string: # we found an occurrence
        occur += 1
        if occur == n: # we found the right occurrence
            unifies, assign, macros = unify(screen, tl, subst.left, tree)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
            if not unifies:
                unifies, assign, macros = unify(screen, tl, subst.right, tree)
                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                if not unifies:
                    return False, tree, n # does not unify, bogus selection
                else:
                    return True, substitute(deepcopy(subst.left), assign), n
            else:
                return True, substitute(deepcopy(subst.right), assign), n
    if isinstance(tree, LRNode):
        found, tree.left, occur = apply_equality(screen, tl, tree.left, string, n, subst, occur)
        if not found:
            found, tree.right, occur = apply_equality(screen, tl, tree.right, string, n, subst, occur)
        return found, tree, occur
    elif isinstance(tree, LeafNode):
        return found, tree, occur
    elif isinstance(tree, TupleNode) or isinstance (tree, FnApplNode):
        for i in range(0, len(tree.args)):
            found, tree.args[i], occur = apply_equality(screen, tl, tree.args[i], string, n, subst, occur)
            if found:
                break
        if not found and isinstance(tree, FnApplNode):
            found, tree.var, occur = apply_equality(screen, tl, tree.var, string, n, subst, occur)
        return found, tree, occur
    raise Exception("Node not dealt with : "+str(type(tree)))

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
    tree1, univs = unquantify(screen, tree1, True)
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
    found, tree, occur = apply_equality(screen, tl, sub_tlist.data[line2], sub_string, n, tree1)
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
    
def clear_tableau(screen, tl):
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
    tl.vars = dict()
    tl.tars = dict()
    tl.constraints_processed = (0, 0, 0)
    tl.sorts_processed = (0, 0, 0)
    pad2.refresh()
    pad1.refresh()
    pad0.refresh()
    screen.focus = screen.pad0
    tl.focus = tl.tlist0
    
canonical_numconstraints = { "\\N" : "\\mathbb{N}",
                       "\\Z" : "\\mathbb{Z}",
                       "\\Q" : "\\mathbb{Q}",
                       "\\R" : "\\mathbb{R}",
                       "\\C" : "\\mathbb{C}"}

def tags_to_list(tags):
    t = tags[6:].split(" ")
    if len(t) == 1 and t[0] == '':
        t = []
    return t

def canonicalise_tags(tags):
    taglist = tags_to_list(tags)
    for i in range(0, len(taglist)):
        tag = taglist[i][1:]
        if tag in canonical_numconstraints:
            taglist[i] = "#"+canonical_numconstraints[tag]
    return "Tags: "+' '.join(taglist)

def filter_titles(titles, c):
    titles2 = []
    for (line, v) in titles:
        if v[0] == c or v[0] == c.upper():
            titles2.append((line, v))
    return titles2

def library_import(screen, tl):
    tags = edit(screen, "Tags: ", 6, True)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with constraint shorthands
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
        stmt = relabel(screen, tl, [], tree, tl.vars)
        ok = process_constraints(screen, stmt, tl.constraints)
        if ok:
            relabel_constraints(screen, tl, stmt)
            append_tree(pad1, tlist1, stmt)
            screen.pad1.refresh()
            screen.focus.refresh()
    library.close()

def library_load(screen, tl):
    tags = edit(screen, "Tags: ", 6, True)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with constraint shorthands
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
    title = edit(screen, "Title: ", 7, True)
    if title == None:
        return
    tags = edit(screen, "Tags: ", 6, True)
    if tags == None:
        return
    tags = canonicalise_tags(tags) # deal with constraint shorthands
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
        elif isinstance(tree, ImpliesNode):
            return AndNode(tree.left, complement(tree.right))
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

def unquantify(screen, tree, positive):
    tree = deepcopy(tree)
    mv = []
    univs = []
    while isinstance(tree, ForallNode):
        mv.append(tree.var.name())
        t = tree
        tree = tree.left
        t.left = None
        univs.append(t)
    tree = skolemize_statement(screen, tree, [], 0, [], [], mv, positive)
    return tree, univs

def target_compatible(screen, tl, ttree, dep_list, j, forward):
    if forward: # return "intersection" of lists
        deps_j = tl.tlist1.dependency(j) # targets provable from j
        if -1 in deps_j:
            return dep_list
        if -1 in dep_list:
            return deps_j
        deps = []
        for d1 in deps_j:
            for d2 in dep_list:
               if d1 < d2:
                   d1, d2 = d2, d1
               if target_depends(screen, tl, ttree, d1, d2):
                   if d1 not in deps:
                       deps.append(d1)
        return deps
    else: # return original list or [] depending if target j is target compatible
        if -1 in dep_list:
            return dep_list
        for d in dep_list:
            if target_depends(screen, tl, ttree, j, d):
                return dep_list
        return None

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
    append_tree(screen.pad1, tlist1.data, complement_tree(tree))
    tlist1.dep[len(tlist1.data) - 1] = line
    # update windows
    tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
    tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()
"""

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
    tree1, univs = unquantify(screen, tree1, False) # remove quantifiers by taking temporary metavars
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
    dep = target_compatible(screen, tl, ttree, dep, line2, forward)
    if not dep:
        screen.dialog("Not target compatible. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return
    if forward:
        qP1, u = unquantify(screen, tree1.left, True)
    else:
        tree1 = relabel(screen, tl, univs, tree1, tl.vars, True)
        qP1, u = unquantify(screen, tree1.right, False)
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
        dep = target_compatible(screen, tl, ttree, dep, line2, forward)
        if not dep:
            screen.dialog("Not target compatible. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
        new_tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
        tree2 = AndNode(tree2, new_tree2)
    qP2 = tree2
    if isinstance(qP2, ImpliesNode):
        # treat P => Q as ¬P \wedge Q
        varlist = deepcopy(tl.vars) # temporary relabelling
        unifies, assign, macros = unify(screen, tl, qP1, complement_tree(relabel(screen, tl, [], deepcopy(qP2.left), varlist)))
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
        if unifies:
            varlist = deepcopy(tl.vars) # assignments in or branches can be independent
            unifies, assign, macros = unify(screen, tl, qP1, relabel(screen, tl, [], deepcopy(qP2.right), varlist), assign)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    else:
        unifies, assign, macros = unify(screen, tl, qP2, qP1)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    if not unifies:
        screen.dialog("Predicate does not match implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return # does not unify, bogus selection
    if forward:
        stmt = substitute(deepcopy(tree1.right), assign)
        stmt = relabel(screen, tl, univs, stmt, tl.vars, True)
        append_tree(screen.pad1, tlist1.data, stmt)
        tlist1.dep[len(tlist1.data) - 1] = dep
    else:
        stmt = substitute(deepcopy(tree1.left), assign)
        if line2 in tl.tars: # we already reasoned from this target
            stmt = complement_tree(stmt)
            append_tree(screen.pad1, tlist1.data, stmt) # add negation to hypotheses
            tlist1.dep[len(tlist1.data) - 1] = dep
        else:
            append_tree(screen.pad2, tlist2.data, stmt)
            add_descendant(ttree, line2, len(tlist2.data) - 1)
            tl.tars[line2] = True
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
    tree1, univs = unquantify(screen, tree1, False)
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
    dep = target_compatible(screen, tl, ttree, dep, line2, forward)
    if not dep:
        screen.dialog("Not target compatible. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return
    tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
    if forward:
        qP1, u = unquantify(screen, tree1.right, False)
        qP1 = complement_tree(qP1)
    else:
        tree1 = relabel(screen, tl, univs, tree1, tl.vars, True)
        qP1 = complement_tree(unquantify(screen, tree1.left, True)[0])
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
        dep = target_compatible(screen, tl, ttree, dep, line2, forward)
        if not dep:
            screen.dialog("Not target compatible. Press Enter to continue.")
            screen.restore_state()
            screen.focus.refresh()
            return
        new_tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
        tree2 = AndNode(tree2, new_tree2)
    qP2 = tree2
    if isinstance(qP2, ImpliesNode):
        # treat P => Q as ¬P \wedge Q
        vars = deepcopy(tl.vars) # temporary relabelling
        unifies, assign, macros = unify(screen, tl, qP1, complement_tree(relabel(screen, tl, [], deepcopy(qP2.left), vars)))
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
        if unifies:
            vars = deepcopy(tl.vars) # assignments in or branches can be independent
            unifies, assign, macros = unify(screen, tl, qP1, relabel(screen, tl, [], deepcopy(qP2.right), vars), assign)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    else:
        unifies, assign, macros = unify(screen, tl, qP2, qP1)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    if not unifies:
        screen.dialog("Predicate does not match implication. Press Enter to continue.")
        screen.restore_state()
        screen.focus.refresh()
        return # does not unify, bogus selection
    if forward:
        stmt = complement_tree(substitute(deepcopy(tree1.left), assign))
        stmt = relabel(screen, tl, univs, stmt, tl.vars, True)
        append_tree(screen.pad1, tlist1.data, stmt)
        tlist1.dep[len(tlist1.data) - 1] = dep
    else:
        stmt = complement_tree(substitute(deepcopy(tree1.right), assign))
        if line2 in tl.tars: # we already reasoned from this target
            stmt = complement_tree(stmt)
            append_tree(screen.pad1, tlist1.data, stmt) # add negation to hypotheses
            tlist1.dep[len(tlist1.data) - 1] = dep
        else:
            append_tree(screen.pad2, tlist2.data, stmt)
            add_descendant(ttree, line2, len(tlist2.data) - 1)
            tl.tars[line2] = True
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

def add_sibling(screen, tl, ttree, i, j):
    for P in ttree.andlist:
        if P.num == i:
            jnode = TargetNode(j)
            ttree.andlist.append(jnode)
            for k in range(len(tl.tlist1.data)): # hyps that prove i also prove j
                if k in tl.tlist1.dep:
                     if i in tl.tlist1.dep[k]: # add j to list
                          tl.tlist1.dep[k].append(j)
            return True
    for P in ttree.andlist:
        if add_sibling(screen, tl, P, i, j):
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
                    stmt = skolemize_statement(screen, tl1[i], deps, depmin, sk, qz, mv, False)
                    replace_tree(screen.pad1, tl1, i, stmt)
                    rollback()
                while isinstance(tl1[i], AndNode):
                    # First check we don't have P \vee P
                    unifies, assign, macros = unify(screen, tl, tl1[i].left, tl1[i].right)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
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
                while len(mv) > m:
                    mv.pop()
        if not tars_done:
            tars_done = True
            while j < len(tl2):
                tl2[j] = skolemize_statement(screen, tl2[j], deps, depmin, sk, qz, mv, True)
                rollback()
                if isinstance(tl2[j], OrNode):
                    append_tree(screen.pad1, tl1, complement_tree(tl2[j].left))
                    hyps_done = False
                    replace_tree(screen.pad2, tl2, j, tl2[j].right)
                    tl.tlist1.dep[len(tl1) - 1] = [j]
                if isinstance(tl2[j], ImpliesNode):
                    left = relabel(screen, tl, [], tl2[j].left, tl.vars, True)
                    append_tree(screen.pad1, tl1, left)
                    hyps_done = False
                    right = relabel(screen, tl, [], tl2[j].right, tl.vars, True)
                    replace_tree(screen.pad2, tl2, j, right)
                    tl.tlist1.dep[len(tl1) - 1] = [j]
                while isinstance(tl2[j], AndNode):
                    # First check we don't have P \wedge P
                    unifies, assign, macros = unify(screen, tl, tl2[j].left, tl2[j].right)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if unifies and not assign:
                        replace_tree(screen.pad1, tl2, j, tl2[j].left)
                    else:
                        append_tree(screen.pad2, tl2, tl2[j].right)
                        replace_tree(screen.pad2, tl2, j, tl2[j].left)
                        add_sibling(screen, tl, ttree, j, len(tl2) - 1)
                if isinstance(tl2[j], NotNode) and isinstance(tl2[j].left, ImpliesNode):
                    append_tree(screen.pad2, tl2, complement_tree(tl2[j].left.right))
                    replace_tree(screen.pad2, tl2, j, tl2[j].left.left)
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

def skolemize_quantifiers(tree, deps, sk, ex):
    if isinstance(tree, ExistsNode):
        if not tree.var.is_metavar and not tree.var.skolemized: # check we didn't already deal with this var
            sk.append((tree.var.name(), len(deps), True))
            ex.append(tree.var)
            return skolemize_quantifiers(tree.left, deps, sk, ex)
        else:
            tree.left, deps, sk, ex = skolemize_quantifiers(tree.left, deps, sk, ex)
            return tree, deps, sk, ex
    elif isinstance(tree, ForallNode):
        deps.append(tree.var)
        tree.left, deps, sk, ex = skolemize_quantifiers(tree.left, deps, sk, ex)
        return tree, deps, sk, ex
    else:
        return tree, deps, sk, ex

def skolemize_statement(screen, tree, deps, depmin, sk, qz, mv, positive, blocked=False):
    d = len(deps)
    s = len(sk)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()
    
    if isinstance(tree, NotNode) and isinstance(tree.left, EqNode):
        neq = NeqNode(tree.left.left, tree.left.right)
        neq.sort = PredSort # may be replacing an already typed node
        return neq
    if isinstance(tree, OrNode):
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, True)
        tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, True)
        return tree
    elif isinstance(tree, ForallNode):
        is_blocked = blocked
        if not blocked:
            if positive:
                deps.append(tree.var)
                qz.append(tree)
            else:
                if not isinstance(tree.left, ImpliesNode) and not \
                       isinstance(tree.left, OrNode):
                    tree.var.is_metavar = True
                    deps.append(tree.var)
                    mv.append(tree.var.name())
                    qz.append(ExistsNode(tree.var, None))
                else:
                    is_blocked = True
        tree.var.constraint = skolemize_statement(screen, tree.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, is_blocked or isinstance(tree.left, IffNode))
        rollback()
        return tree.left if not is_blocked else tree    
    elif isinstance(tree, ExistsNode):
        is_blocked = blocked
        if not blocked:
            sk.append((tree.var.name(), len(deps), False))
            domain_constraints = [v.var.constraint if isinstance(v, ForallNode) else v.constraint for v in deps[depmin:]]
            if len(domain_constraints) > 1:
                fn_constraint = FunctionConstraint(DomainTuple(domain_constraints), SetOfNode(tree.var.constraint))
            elif len(domain_constraints) == 1:
                fn_constraint = FunctionConstraint(domain_constraints[0], SetOfNode(tree.var.constraint))
            else:
                fn_constraint = FunctionConstraint(None, SetOfNode(tree.var.constraint))
            if positive:
                if not blocked:
                    tree.var.is_metavar = True
                    mv.append(tree.var.name())
                    v = VarNode(tree.var.name(), fn_constraint, True)
                    qz.append(ExistsNode(v, None))
                if isinstance(tree.left, ImpliesNode) or isinstance(tree.left, OrNode):
                    is_blocked = True
            else:
                v = VarNode(tree.var.name(), fn_constraint, False)
                qz.append(ForallNode(v, None))
        tree.var.constraint = skolemize_statement(screen, tree.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, is_blocked)
        rollback()
        return tree.left if not blocked else tree
    elif isinstance(tree, SetBuilderNode):
        if not blocked:
            if positive:
                deps.append(tree.left.left)
            else:
                tree.left.left.is_metavar = True
                deps.append(tree.left.left) # free
                mv.append(tree.left.left.name())
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, blocked)
        tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, IffNode) or isinstance(tree, ImpliesNode):
        is_blocked = blocked or isinstance(tree, IffNode)
        t = tree
        while isinstance(t.left, ForallNode) or isinstance(t.left, ExistsNode):
            t.left.var.constraint = skolemize_statement(screen, t.left.var.constraint, deps, depmin, sk, qz, mv, not positive, is_blocked)
            t = t.left
        t.left = skolemize_statement(screen, t.left, deps, depmin, sk, qz, mv, not positive, is_blocked)
        if not isinstance(tree.right, ForallNode) and not isinstance(tree.right, ExistsNode):
            tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, is_blocked)
        else:
            tree.right.var.constraint = skolemize_statement(screen, tree.right.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
            t = tree.right
            while isinstance(t.left, ForallNode) or isinstance(t.left, ExistsNode):
                t.left.var.constraint = skolemize_statement(screen, t.left.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
                t = t.left
            t.left = skolemize_statement(screen, t.left, deps, depmin, sk, qz, mv, positive, is_blocked)
        rollback()
        return tree
    elif isinstance(tree, LRNode):
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, blocked)
        tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, VarNode):
        is_meta = False
        if tree.name() in mv:
            is_meta = True
            tree.is_metavar = True
        n, is_orig = skolem_deps(tree.name(), sk)
        if n == -1: # not a skolem variable
            return tree
        else:
            depstart = 0 if is_orig else depmin
            fn_args = [VarNode(deps[i].name(), deps[i].constraint, deps[i].is_metavar) \
                    for i in range(depstart, n)]
            fn = FnApplNode(VarNode(tree.name()), fn_args)
            fn.is_skolem = True
            if is_meta:
                fn.is_metavar = True
                fn.var.is_metavar = True
            fn.sort = tree.sort # may be replacing an already typed node
            fn.var.sort = tree.sort # may be replacing an already typed node
            return fn
    elif isinstance(tree, FnApplNode):
        if tree.name() in mv:
            tree.is_metavar = True
            tree.var.is_metavar = True
        n, is_orig = skolem_deps(tree.name(), sk)
        if n != -1 and not tree.is_skolem: # skolem variable not already skolemized
            tree.var = skolemize_statement(screen, tree.var, deps, depmin, sk, qz, mv, positive, blocked)
            rollback()
        for i in range(0, len(tree.args)):
            tree.args[i] = skolemize_statement(screen, tree.args[i], deps, depmin, sk, qz, mv, positive, blocked)
            rollback()
        return tree
    elif isinstance(tree, TupleNode):
        for i in range(0, len(tree.args)):
            tree.args[i] = skolemize_statement(screen, tree.args[i], deps, depmin, sk, qz, mv, positive, blocked)
            rollback()
        return tree
    elif isinstance(tree, SetSort):
        tree.sort = skolemize_statement(screen, tree.sort, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, TupleSort):
        for i in range(len(tree.sorts)):
            tree.sorts[i] = skolemize_statement(screen, tree.sorts[i], deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, CartesianConstraint):
        for i in range(len(tree.sorts)):
            tree.sorts[i] = skolemize_statement(screen, tree.sorts[i], deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset':
        tree.constraint = skolemize_statement(screen, tree.constraint, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    else:
        return tree
        
def skolem_deps(name, sk):
    for (v, n, is_orig) in sk:
        if v == name:
            return n, is_orig
    return -1, False
