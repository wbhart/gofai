from copy import deepcopy
from nodes import LRNode, VarNode, NaturalNode, FnApplNode, ExpNode, AddNode, \
                  SubNode, MulNode, DivNode, IntersectNode, UnionNode, \
                  DiffNode, SymbolNode, TupleNode, PowerSetNode, AndNode, \
                  OrNode, ElemNode, EqNode, NeqNode, LtNode, GtNode, \
                  LeqNode, GeqNode, SubseteqNode, SubsetneqNode, \
                  SupseteqNode, SupsetneqNode, ImpliesNode, IffNode, \
                  NotNode, ForallNode, ExistsNode, BoolNode, TupleComponentNode, \
                  SetBuilderNode, LambdaNode, mark_binder_vars
from utility import sorts_equal, find_sort, sorts_compatible, coerce_sorts
from sorts import Sort, PredSort, SetSort, TupleSort, NumberSort, Universum, \
                  CartesianConstraint

def is_expression(tree):
    if isinstance(tree, VarNode) or isinstance(tree, NaturalNode) \
       or isinstance(tree, FnApplNode) or isinstance(tree, ExpNode) \
       or isinstance(tree, AddNode) or isinstance(tree, SubNode) \
       or isinstance(tree, MulNode) or isinstance(tree, DivNode) \
       or isinstance(tree, IntersectNode) or isinstance(tree, UnionNode) \
       or isinstance(tree, DiffNode) or isinstance(tree, PowerSetNode) \
       or isinstance(tree, SymbolNode) or isinstance(tree, LambdaNode) \
       or isinstance(tree, TupleComponentNode) or isinstance(tree, Sort):
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
            return False, [], []
    if (isinstance(tree1, VarNode) or isinstance(tree1, FnApplNode)) \
           and tree1.is_metavar:
        if isinstance(tree2, Sort) and isinstance(tree1.sort, SetSort) and \
           isinstance(tree1.sort.sort, Universum):
            assign.append(deepcopy((tree1, tree2)))
        elif (isinstance(node_constraint(tree1), PredSort) and is_predicate(tree2)) \
              or (not isinstance(node_constraint(tree1), PredSort) and is_expression(tree2)
              and (tree1.is_binder or not tree_contains_binder(tree2))):
                  if sorts_compatible(screen, tl, tree1.sort, tree2.sort, assign):
                      if not isinstance(tree2, VarNode) or tree1.name() != tree2.name():
                           assign.append(deepcopy((tree1, tree2)))
                  else:
                      return False, [], []
        else:
            return False, [], []
    elif (isinstance(tree2, VarNode) or isinstance(tree2, FnApplNode)) \
           and tree2.is_metavar:
        if isinstance(tree1, Sort) and isinstance(tree2.sort, SetSort) and \
           isinstance(tree2.sort.sort, Universum):
            assign.append(deepcopy((tree2, tree1)))
        elif (isinstance(node_constraint(tree2), PredSort) and is_predicate(tree1)) \
            or (not isinstance(node_constraint(tree2), PredSort) and is_expression(tree1)
            and (tree2.is_binder or not tree_contains_binder(tree1))):
              if sorts_compatible(screen, tl, tree2.sort, tree1.sort, assign):
                  if not isinstance(tree1, VarNode) or tree2.name() != tree1.name():
                       assign.append(deepcopy((tree2, tree1)))
              else:
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
        if isinstance(tree2, Sort) or (isinstance(tree2, VarNode) and \
           isinstance(tree2.sort, SetSort)):
            pass
            # TODO: do assignment of metavariable (type variable)
        else:
            return False, [], []
    elif isinstance(tree2, Universum):
        if isinstance(tree1, Sort) or (isinstance(tree1, VarNode) and \
           isinstance(tree1.sort, SetSort)):
            pass
            # TODO: do assignment of metavariable (type variable)
        else:
            return False, [], []
    else: # we didn't hit a variable, or a pair of functions or a type variable
        if type(tree1) != type(tree2):
            return False, [], []
        elif isinstance(tree1, NaturalNode) or isinstance(tree1, BoolNode):
            if tree1.value == tree2.value:
                return True, assign, macros
            else:
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
            if len(tree1.sorts) != len(tree2.sorts):
                return False, [], []
            for i in range(len(tree1.sorts)):
                unified, assign, macros = trees_unify(screen, tl, tree1.sorts[i], tree2.sorts[i], assign, macros)
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

def subst(tree1, var, tree2):
    if tree1 == None:
        return tree1
    if isinstance(tree1, ForallNode) or isinstance(tree1, ExistsNode):
        tree1.var.constraint = subst(tree1.var.constraint, var, tree2)
        if isinstance(tree1.var.constraint, TupleSort):
            tree1.var.constraint = CartesianConstraint(tree1.var.constraint.sorts)
        tree1.left = subst(tree1.left, var, tree2)
        return tree1
    if isinstance(tree1, VarNode):
        tree1.constraint = subst(tree1.constraint, var, tree2)
        if tree1.name() == var.name():
            return deepcopy(tree2)
        else:
            return tree1
    elif isinstance(tree1, TupleComponentNode):
        # special hack to expand (a, b)[0] as function application
        if isinstance(tree1.left, VarNode) and tree1.left.name() == var.name() \
             and isinstance(tree2, TupleNode):
            n = tree1.right.value
            if n >= len(tree2.args):
                raise Exception("Invalid indexing in tuple")
            return tree2.args[n]
        p = deepcopy(tree1)
        p.left = subst(p.left, var, tree2)
        return p
    elif isinstance(tree1, FnApplNode):
        if tree1.name() == var.name() and is_predicate(tree2):
            p = deepcopy(tree2)
            for i in range(0, len(tree1.args)):
                p = subst(p, var.args[i], tree1.args[i])
            return p
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
        tree1.constraint = subst(tree1.constraint, var, tree2)
        return tree1
    elif isinstance(tree1, SetSort):
        if tree1.sort != tree1:
            tree1.sort = subst(tree1.sort, var, tree2)
        return tree1
    elif isinstance(tree1, TupleSort):
        for i in range(len(tree1.sorts)):
            tree1.sorts[i] = subst(tree1.sorts[i], var, tree2)
        return tree1
    elif isinstance(tree1, CartesianConstraint):
        for i in range(len(tree1.sorts)):
            tree1.sorts[i] = subst(tree1.sorts[i], var, tree2)
        return tree1
    else:
        return tree1

def make_substitution(assign1, assign2):
    (var1, expr1) = assign1
    (var2, expr2) = assign2

    var1 = subst(deepcopy(var1), var2, expr2) # in case it is a function
    return (var1, subst(deepcopy(expr1), var2, expr2))

def substitute(tree, assign):
   for (var, val) in assign:
       tree = subst(tree, var, val)
   return tree
    
def is_function_type(sort):
    return isinstance(sort, SetSort) and isinstance(sort.sort, TupleSort) and \
                   len(sort.sort.sorts) == 2
