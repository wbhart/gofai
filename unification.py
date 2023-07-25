from copy import deepcopy
from nodes import LRNode, VarNode, NaturalNode, FnNode, ExpNode, AddNode, \
                  SubNode, MulNode, DivNode, IntersectNode, UnionNode, \
                  DiffNode, SymbolNode, TupleNode, PowerSetNode, AndNode, \
                  OrNode, ElemNode, EqNode, NeqNode, LtNode, GtNode, \
                  LeqNode, GeqNode, SubseteqNode, SubsetneqNode, \
                  SupseteqNode, SupsetneqNode, ImpliesNode, IffNode, \
                  NotNode, ForallNode, ExistsNode, BoolNode, \
                  SetBuilderNode, LambdaNode, mark_binder_vars

from sorts import PredSort

def is_expression(tree):
    if isinstance(tree, VarNode) or isinstance(tree, NaturalNode) \
       or isinstance(tree, FnNode) or isinstance(tree, ExpNode) \
       or isinstance(tree, AddNode) or isinstance(tree, SubNode) \
       or isinstance(tree, MulNode) or isinstance(tree, DivNode) \
       or isinstance(tree, IntersectNode) or isinstance(tree, UnionNode) \
       or isinstance(tree, DiffNode) or isinstance(tree, PowerSetNode) \
       or isinstance(tree, SymbolNode) or isinstance(tree, LambdaNode):
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
    elif isinstance(tree, FnNode):
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
    elif isinstance(tree, FnNode):
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

def trees_unify(tree1, tree2, assigned=[], macro=[]):
    assign = deepcopy(assigned) # default params are mutable
    macros = deepcopy(macro)
    # special case to deal with unexpanded macros
    if isinstance(tree1, FnNode) and (tree1.name() == 'universe' \
                   or tree1.name == 'domain' or tree1.name == 'codomain'):
        macros.append((tree2, tree1))
        return True, assign, macros
    if isinstance(tree2, FnNode) and (tree2.name() == 'universe'\
                   or tree2.name == 'domain' or tree2.name == 'codomain'):
        macros.append((tree1, tree2))
        return True, assign, macros
    if isinstance(tree1, FnNode) and isinstance(tree2, FnNode) \
           and tree1.is_metavar:
        if len(tree1.args) != len(tree2.args):
            return False, [], []
        for i in range(0, len(tree1.args)):
            unifies, assign, macros = trees_unify(tree1.args[i], tree2.args[i], assign, macros)
            if not unifies:
                return False, [], []
        assign.append(deepcopy((tree1.var, tree2.var)))
        return True, assign, macros
    if isinstance(tree1, FnNode) and isinstance(tree2, FnNode) \
           and tree2.is_metavar:
        if len(tree1.args) != len(tree2.args):
            return False, [], []
        for i in range(0, len(tree1.args)):
            unifies, assign, macros = trees_unify(tree2.args[i], tree1.args[i], assign, macros)
            if not unifies:
                return False, [], []
        assign.append(deepcopy((tree2.var, tree1.var)))
        return True, assign, macros
    if (isinstance(tree1, VarNode) or isinstance(tree1, FnNode)) \
           and tree1.is_metavar:
        if (isinstance(node_constraint(tree1), PredSort) and is_predicate(tree2)) \
              or (not isinstance(node_constraint(tree1), PredSort) and is_expression(tree2)
              and (tree1.is_binder or not tree_contains_binder(tree2))):
            assign.append(deepcopy((tree1, tree2)))
        else:
            return False, [], []
    elif (isinstance(tree2, VarNode) or isinstance(tree2, FnNode)) \
           and tree2.is_metavar:
        if (isinstance(node_constraint(tree2), PredSort) and is_predicate(tree1)) \
              or (not isinstance(node_constraint(tree2), PredSort) and is_expression(tree1)
              and (tree2.is_binder or not tree_contains_binder(tree1))):
            assign.append(deepcopy((tree2, tree1)))
        else:
            return False, [], []
    elif isinstance(tree1, VarNode) or isinstance(tree2, VarNode):
        if not isinstance(tree1, VarNode) or not isinstance(tree2, VarNode):
            return False, [], []
        if tree1.name() != tree2.name(): # if not metavars check names
            return False, [], []
    elif isinstance(tree1, FnNode) and isinstance(tree2, FnNode):
        unified, assign, macros = trees_unify(tree1.var, tree2.var, assign, macros)
        if not unified:
            return False, [], []
        if len(tree1.args) != len(tree2.args):
            return False, [], []
        for i in range(0, len(tree1.args)):
            unified, assign, macros = trees_unify(tree1.args[i], tree2.args[i], assign, macros)
            if not unified:
                return False, [], []
    elif isinstance(tree1, LambdaNode) and isinstance(tree2, LambdaNode):
        t1 = deepcopy(tree1)
        t2 = deepcopy(tree2)
        var1 = t1.left
        var2 = t2.left
        mark_binder_vars(t1, var1)
        mark_binder_vars(t2, var2)
        unified, assign, macros = trees_unify(var1, var2, assign, macros)
        if not unified:
            return False, [], []
        unified, assign, macros = trees_unify(t1.right, t2.right, assign, macros)
        if not unified:
            return False, [], []
    elif isinstance(tree1, EqNode) and isinstance(tree2, EqNode):
        # special case for equality, try both directions
        ass = deepcopy(assign)
        mac = deepcopy(macros)
        unified, ass, mac = trees_unify(tree1.left, tree2.left, ass, mac)
        if unified:
            unified, ass, mac = trees_unify(tree1.right, tree2.right, ass, mac)
        if not unified: # try the other way around
            unified, assign, macros = trees_unify(tree1.left, tree2.right, assign, macros)
            if not unified:
                return False, [], []
            unified, assign, macros = trees_unify(tree1.right, tree2.left, assign, macros)
            if not unified:
                return False, [], []
        else:
            assign = ass
            macros = mac
    else: # we didn't hit a variable, or a pair of functions
        if type(tree1) != type(tree2):
            return False, [], []
        elif isinstance(tree1, SymbolNode):
            if tree1.name() != tree2.name():
                return False, [], []
            if tree1.name() == '\\emptyset':
                unified, assign, macros = trees_unify(tree1.constraint.universe, tree2.constraint.universe, assign, macros)
                if not unified:
                    return False, [], []
        elif isinstance(tree1, TupleNode):
            if len(tree1.args) != len(tree2.args):
                return False, [], []
            for i in range(0, len(tree1.args)):
                unified, assign, macros = trees_unify(tree1.args[i], tree2.args[i], assign, macros)
                if not unified:
                    return False, [], []
        elif isinstance(tree1, LRNode):
            unified, assign, macros = trees_unify(tree1.left, tree2.left, assign, macros)
            if not unified:
                return False, [], []
            unified, assign, macros = trees_unify(tree1.right, tree2.right, assign, macros)
            if not unified:
                return False, [], []
    # if any case falls through, unification occurred successfully
    return True, assign, macros

def unify(tree1, tree2, assigned=[]):
    assign = deepcopy(assigned) # default params are mutable
    unified, assign, macros = trees_unify(tree1, tree2, assign)
    if not unified:
        return False, [], []
    i = 0
    while i < len(assign):
        for j in range(0, i):
            assign[j] = make_substitution(assign[j], assign[i])
        j = i + 1
        while j < len(assign):
            if assign[i][0].name() == assign[j][0].name():
                unified, assign, macros = trees_unify(assign[i][1], assign[j][1], assign, macros)
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
    elif isinstance(tree1, FnNode):
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
        if not isinstance(p.var, VarNode) and not isinstance(p.var, FnNode):
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
        tree1.constraint.universe = subst(tree1.constraint.universe, var, tree2)
        return tree1
    else:
        return tree1

def make_substitution(assign1, assign2):
    (var1, expr1) = assign1
    (var2, expr2) = assign2

    var1 = subst(deepcopy(var1), var2, expr2) # in case it is a function
    return (var1, subst(deepcopy(expr1), var2, expr2))