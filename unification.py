from copy import deepcopy
from nodes import LRNode, VarNode, NaturalNode, FnApplNode, ExpNode, AddNode, \
                  SubNode, MulNode, DivNode, IntersectNode, UnionNode, \
                  DiffNode, SymbolNode, TupleNode, PowerSetNode, AndNode, \
                  OrNode, ElemNode, EqNode, NeqNode, LtNode, GtNode, \
                  LeqNode, GeqNode, SubseteqNode, SubsetneqNode, \
                  SupseteqNode, SupsetneqNode, ImpliesNode, IffNode, \
                  NotNode, ForallNode, ExistsNode, BoolNode, TupleComponentNode, \
                  SetBuilderNode, LambdaNode, mark_binder_vars

from sorts import Sort, PredSort, SetSort, TupleSort, NumberSort, Universum

def is_expression(tree):
    if isinstance(tree, VarNode) or isinstance(tree, NaturalNode) \
       or isinstance(tree, FnApplNode) or isinstance(tree, ExpNode) \
       or isinstance(tree, AddNode) or isinstance(tree, SubNode) \
       or isinstance(tree, MulNode) or isinstance(tree, DivNode) \
       or isinstance(tree, IntersectNode) or isinstance(tree, UnionNode) \
       or isinstance(tree, DiffNode) or isinstance(tree, PowerSetNode) \
       or isinstance(tree, SymbolNode) or isinstance(tree, LambdaNode) \
       or isinstance(tree, TupleComponentNode):
        return True
    else:
        return True

def is_predicate(tree):
    if isinstance(tree, AndNode) or isinstance(tree, OrNode) \
       or isinstance(tree, ElemNode) or isinstance(tree, EqNode) \
       or isinstance(tree, NeqNode) or isinstance(tree, LtNode) \
       or isinstance(tree, GtNode) or isinstance(tree, GeqNode) \
       or isinstance(tree, LeqNode) or isinstance(tree, SubseteqNode) \
       or isinstance(tree, SubsetneqNode) or isinstance(tree, SupseteqNode) \
       or isinstance(tree, SupsetneqNode) or isinstance(tree, ImpliesNode) \
       or isinstance(tree, IffNode) or isinstance(tree, NotNode) \
       or isinstance(tree, ForallNode) or isinstance(tree, ExistsNode) \
       or isinstance(tree, BoolNode):
        return True
    else:
        return False

def node_constraint(tree):
    if isinstance(tree, VarNode):
        return tree.constraint
    elif isinstance(tree, FnApplNode):
        return tree.var.constraint
    else:
        return None

def tree_contains_binder(tree, ignorevars=[]):
    ignore = deepcopy(ignorevars) # default params are mutable
    if tree == None:
        return False
    elif isinstance(tree, SetBuilderNode):
        ignore.append(tree.left.left.name)
    elif isinstance(tree, VarNode):
        return tree.is_binder and tree.name() not in ignore
    elif isinstance(tree, LRNode):
        return tree_contains_binder(tree.left, ignore) or \
               tree_contains_binder(tree.right, ignore)
    elif isinstance(tree, FnApplNode):
        if tree.is_binder and tree.name() not in ignore:
            return True
        for i in range(0, len(tree.args)):
            if tree_contains_binder(tree.args[i], ignore):
                return True
    elif isinstance(tree, TupleNode):
        for i in range(0, len(tree.args)):
            if tree_contains_binder(tree.args[i], ignore):
                return True
    return False # all other cases

def trees_unify(screen, tl, tree1, tree2, assigned=[], macro=[]):
    assign = deepcopy(assigned) # default params are mutable
    macros = deepcopy(macro)
    # special case to deal with unexpanded macros
    if isinstance(tree1, FnApplNode) and (tree1.name() == 'universe' \
                   or tree1.name == 'domain' or tree1.name == 'codomain'):
        macros.append((tree2, tree1))
        return True, assign, macros
    if isinstance(tree2, FnApplNode) and (tree2.name() == 'universe'\
                   or tree2.name == 'domain' or tree2.name == 'codomain'):
        macros.append((tree1, tree2))
        return True, assign, macros
    if isinstance(tree1, FnApplNode) and isinstance(tree2, FnApplNode) \
           and tree1.is_metavar:
        if len(tree1.args) != len(tree2.args):
            return False, [], []
        for i in range(0, len(tree1.args)):
            unifies, assign, macros = trees_unify(screen, tl, tree1.args[i], tree2.args[i], assign, macros)
            if not unifies:
                return False, [], []
        if sorts_compatible(screen, tl, tree1.var.sort, tree2.var.sort):
            assign.append(deepcopy((tree1.var, tree2.var)))
            return True, assign, macros
        else:
            screen.dialog(str(tree1.var)+", "+str(tree2.var)+" : "+str(tree1.var.sort)+", "+str(tree2.var.sort))
            screen.dialog(str(tree1.var.constraint)+", "+str(tree2.var.constraint))
            return False, [], []
    if isinstance(tree1, FnApplNode) and isinstance(tree2, FnApplNode) \
           and tree2.is_metavar:
        if len(tree1.args) != len(tree2.args):
            return False, [], []
        for i in range(0, len(tree1.args)):
            unifies, assign, macros = trees_unify(screen, tl, tree2.args[i], tree1.args[i], assign, macros)
            if not unifies:
                return False, [], []
        if sorts_compatible(screen, tl, tree2.var.sort, tree1.var.sort):
            assign.append(deepcopy((tree2.var, tree1.var)))
            return True, assign, macros
        else:
            screen.dialog(str(tree1.var)+", "+str(tree2.var)+" : "+str(tree1.var.sort)+", "+str(tree2.var.sort))
            screen.dialog(str(tree1.var.constraint)+", "+str(tree2.var.constraint))
            return False, [], []
    if (isinstance(tree1, VarNode) or isinstance(tree1, FnApplNode)) \
           and tree1.is_metavar:
        if (isinstance(node_constraint(tree1), PredSort) and is_predicate(tree2)) \
              or (not isinstance(node_constraint(tree1), PredSort) and is_expression(tree2)
              and (tree1.is_binder or not tree_contains_binder(tree2))):
                  if sorts_compatible(screen, tl, tree1.sort, tree2.sort):
                      assign.append(deepcopy((tree1, tree2)))
                  else:
                      screen.dialog(str(tree1)+", "+str(tree2)+" : "+str(tree1.sort)+", "+str(tree2.sort))
                      return False, [], []
        else:
            return False, [], []
    elif (isinstance(tree2, VarNode) or isinstance(tree2, FnApplNode)) \
           and tree2.is_metavar:
        if (isinstance(node_constraint(tree2), PredSort) and is_predicate(tree1)) \
              or (not isinstance(node_constraint(tree2), PredSort) and is_expression(tree1)
              and (tree2.is_binder or not tree_contains_binder(tree1))):
              if sorts_compatible(screen, tl, tree1.sort, tree2.sort):
                  assign.append(deepcopy((tree2, tree1)))
              else:
                  screen.dialog(str(tree1)+", "+str(tree2)+" : "+str(tree1.sort)+", "+str(tree2.sort))
                  return False, [], []
        else:
            return False, [], []
    elif isinstance(tree1, VarNode) or isinstance(tree2, VarNode):
        if not isinstance(tree1, VarNode) or not isinstance(tree2, VarNode):
            return False, [], []
        if tree1.name() != tree2.name(): # if not metavars check names
            return False, [], []
    elif isinstance(tree1, FnApplNode) and isinstance(tree2, FnApplNode):
        unified, assign, macros = trees_unify(screen, tl, tree1.var, tree2.var, assign, macros)
        if not unified:
            return False, [], []
        if len(tree1.args) != len(tree2.args):
            return False, [], []
        for i in range(0, len(tree1.args)):
            unified, assign, macros = trees_unify(screen, tl, tree1.args[i], tree2.args[i], assign, macros)
            if not unified:
                return False, [], []
    elif isinstance(tree1, LambdaNode) and isinstance(tree2, LambdaNode):
        t1 = deepcopy(tree1)
        t2 = deepcopy(tree2)
        var1 = t1.left
        var2 = t2.left
        mark_binder_vars(t1, var1)
        mark_binder_vars(t2, var2)
        unified, assign, macros = trees_unify(screen, tl, var1, var2, assign, macros)
        if not unified:
            return False, [], []
        unified, assign, macros = trees_unify(screen, tl, t1.right, t2.right, assign, macros)
        if not unified:
            return False, [], []
    elif isinstance(tree1, EqNode) and isinstance(tree2, EqNode):
        # special case for equality, try both directions
        ass = deepcopy(assign)
        mac = deepcopy(macros)
        unified, ass, mac = trees_unify(screen, tl, tree1.left, tree2.left, ass, mac)
        if unified:
            unified, ass, mac = trees_unify(screen, tl, tree1.right, tree2.right, ass, mac)
        if not unified: # try the other way around
            unified, assign, macros = trees_unify(screen, tl, tree1.left, tree2.right, assign, macros)
            if not unified:
                return False, [], []
            unified, assign, macros = trees_unify(screen, tl, tree1.right, tree2.left, assign, macros)
            if not unified:
                return False, [], []
        else:
            assign = ass
            macros = mac
    elif isinstance(tree1, Universum):
        if isinstance(tree2, Sort) or (isinstance(tree2, VarNode) and is_set_sort(tree2.sort)):
            pass
            # TODO: do assignment of metavariable (type variable)
        else:
            screen.dialog(str(tree1)+" , "+str(tree2))
            return False, [], []
    elif isinstance(tree2, Universum):
        if isinstance(tree1, Sort) or (isinstance(tree1, VarNode) and is_set_sort(tree1.sort)):
            pass
            # TODO: do assignment of metavariable (type variable)
        else:
            screen.dialog(str(tree1)+" , "+str(tree2))
            return False, [], []
    else: # we didn't hit a variable, or a pair of functions or a type variable
        if type(tree1) != type(tree2):
            return False, [], []
        elif isinstance(tree1, SymbolNode):
            if tree1.name() != tree2.name():
                return False, [], []
            if tree1.name() == '\\emptyset':
                unified, assign, macros = trees_unify(screen, tl, tree1.sort, tree2.sort, assign, macros)
                if not unified:
                    return False, [], []
        elif isinstance(tree1, SetSort):
            if tree1.sort == tree1:
                return (tree2.sort == tree2 and tree1 == tree2), assign, macros
            if tree2.sort == tree2:
                return False, [], []
            unified, assign, macros = trees_unify(screen, tl, tree1.sort, tree2.sort, assign, macros)
            if not unified:
                return False, [], []
        elif isinstance(tree1, TupleSort):
            if len(tree1.sets) != len(tree2.sets):
                return False, [], []
            for i in range(len(tree1.sets)):
                unified, assign, macros = trees_unify(screen, tl, tree1.sets[i], tree2.sets[i], assign, macros)
                if not unified:
                    return False, [], []
        elif isinstance(tree1, TupleNode):
            if len(tree1.args) != len(tree2.args):
                return False, [], []
            for i in range(0, len(tree1.args)):
                unified, assign, macros = trees_unify(screen, tl, tree1.args[i], tree2.args[i], assign, macros)
                if not unified:
                    return False, [], []
        elif isinstance(tree1, LRNode):
            unified, assign, macros = trees_unify(screen, tl, tree1.left, tree2.left, assign, macros)
            if not unified:
                return False, [], []
            unified, assign, macros = trees_unify(screen, tl, tree1.right, tree2.right, assign, macros)
            if not unified:
                return False, [], []
    # if any case falls through, unification occurred successfully
    return True, assign, macros

def unify(screen, tl, tree1, tree2, assigned=[]):
    assign = deepcopy(assigned) # default params are mutable
    unified, assign, macros = trees_unify(screen, tl, tree1, tree2, assign)
    if not unified:
        return False, [], []
    i = 0
    while i < len(assign):
        for j in range(0, i):
            assign[j] = make_substitution(assign[j], assign[i])
        j = i + 1
        while j < len(assign):
            if assign[i][0].name() == assign[j][0].name():
                unified, assign, macros = trees_unify(screen, tl, assign[i][1], assign[j][1], assign, macros)
                if not unified:
                    return False, [], []
                del assign[j]
            else:
                assign[j] = make_substitution(assign[j], assign[i])
                j += 1
        i += 1
    return True, assign, macros

def subst(tree1, var, tree2):
    if tree1 == None:
        return tree1
    if isinstance(tree1, ForallNode) or isinstance(tree1, ExistsNode):
        tree1.var.constraint = subst(tree1.var.constraint, var, tree2)
        tree1.left = subst(tree1.left, var, tree2)
        return tree1
    if isinstance(tree1, VarNode):
        if tree1.name() == var.name():
            return deepcopy(tree2)
        else:
            return tree1
    elif isinstance(tree1, FnApplNode):
        if tree1.name() == var.name() and is_predicate(tree2):
            p = deepcopy(tree2)
            for i in range(0, len(tree1.args)):
                p = subst(p, var.args[i], tree1.args[i])
            return p
        # TODO : come up with a proper Pair signature
        # This is an unsound hack to allow pairs to be
        # treated like functions
        if tree1.name() == var.name() and isinstance(tree2, TupleNode):
            if isinstance(tree1.args[0], NaturalNode):
                n = tree1.args[0].value
                if n >= len(tree2.args):
                    raise Exception("Invalid indexing in tuple")
                return tree2.args[n]
            else:
                raise Exception("Tuple is not a general function")
        p = deepcopy(tree1)
        p.var = subst(p.var, var, tree2)
        if not isinstance(p.var, VarNode) and not isinstance(p.var, FnApplNode):
            p.is_metavar = False
        elif tree1.name() == var.name(): # we did substitution
            p.is_metavar = tree2.is_metavar
        for i in range(0, len(p.args)):
            p.args[i] = subst(p.args[i], var, tree2)
        return p
    elif isinstance(tree1, TupleNode):
        args = [subst(t, var, tree2) for t in tree1.args]
        return TupleNode(args)
    elif isinstance(tree1, LRNode):
        tree1.left = subst(tree1.left, var, tree2)
        tree1.right = subst(tree1.right, var, tree2)
        return tree1
    elif isinstance(tree1, SymbolNode) and tree1.name() == '\\emptyset':
        tree1.sort = subst(tree1.sort, var, tree2)
        return tree1
    elif isinstance(tree1, SetSort):
        if tree1.sort != tree1:
            tree1.sort = subst(tree1.sort, var, tree2)
        return tree1
    elif isinstance(tree1, TupleSort):
        for i in range(len(tree1.sets)):
            tree1.sets[i] = subst(tree1.sets[i], var, tree2)
        return tree1
    else:
        return tree1

def make_substitution(assign1, assign2):
    (var1, expr1) = assign1
    (var2, expr2) = assign2

    var1 = subst(deepcopy(var1), var2, expr2) # in case it is a function
    return (var1, subst(deepcopy(expr1), var2, expr2))

class SortNode:
    def __init__(self, sort):
        self.sort = sort
        self.subsorts = []

def find_sort(screen, tl, stree, s):
        if sorts_equal(s, stree.sort):
            return stree
        for t in stree.subsorts:
            r = find_sort(screen, tl, t, s)
            if r:
                return r
        return None

def insert_sort(screen, tl, s1, s2):
    # make s2 a subsort of s1
    r = find_sort(screen, tl, tl.stree, s1)
    r.subsorts.append(SortNode(s2))

def sort_type_class(sort):
    if isinstance(sort, VarNode):
        return sort.constraint.typeclass
    elif isinstance(sort, NumberSort):
        return sort.typeclass
    else:
        raise Exception("Not a valid sort")
    
def is_function_type(sort):
    return isinstance(sort, SetSort) and isinstance(sort.sort, TupleSort) and \
                   len(sort.sort.sets) == 2

def is_set_sort(sort):
    return isinstance(sort, SetSort) or isinstance(sort, NumberSort)

def sorts_equal(s1, s2):
    if type(s1) != type(s2):
        return False
    elif isinstance(s1, VarNode) or isinstance(s1, NumberSort):
        return s1.name() == s2.name()
    elif isinstance(s1, SetSort):
        return sorts_equal(s1.sort, s2.sort)
    elif isinstance(s1, TupleSort):
        if len(s1.sets) != len(s2.sets):
            return False
        for i in range(len(s1.sets)):
            if not sorts_equal(s1.sets[i], s2.sets[i]):
                return False
        return True
    elif isinstance(s1, PredSort) or isinstance(s1, Universum):
        return True
    return False

def coerce_sorts(screen, tl, s1, s2):
    # if s2 can be coerced to s1, return s1, else None
    if sorts_equal(s1, s2):
        return s1
    b = find_sort(screen, tl, tl.stree, s1)
    if b:
        r = find_sort(screen, tl, b, s2)
        if r:
            return s1
    return None # not coercible
    
def sorts_compatible(screen, tl, s1, s2):
    t1 = isinstance(s1, TupleSort)
    t2 = isinstance(s2, TupleSort)
    if (t1 and not t2) or (t2 and not t1):
        return False
    if t1:
        if len(s1.sets) != len(s2.sets):
            return False 
        compatible = True
        for i in range(len(s1.sets)):
            if not coerce_sorts(screen, tl, s1.sets[i], s2.sets[i]):
                compatible = False
                break
        if not compatible:
            compatible = True
            for i in range(len(s1.sets)):
                if not coerce_sorts(screen, tl, s2.sets[i], s1.sets[i]):
                    compatible = False
                    break
        return compatible
    c1 = isinstance(s1, SetSort)
    c2 = isinstance(s2, SetSort)
    if (c1 and not c2) or (c2 and not c1):
         return False
    if c1:
         return sorts_compatible(screen, tl, s1.sort, s2.sort)
    if coerce_sorts(screen, tl, s1, s2):
        return True
    if coerce_sorts(screen, tl, s2, s1):
        return True
    return False