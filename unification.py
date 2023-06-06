from copy import deepcopy
from nodes import LRNode, VarNode, NaturalNode, FnNode, ExpNode, AddNode, \
                  SubNode, MulNode, DivNode, IntersectNode, UnionNode, \
                  DiffNode, SymbolNode, TupleNode

def is_expression(tree):
    if isinstance(tree, VarNode) or isinstance(tree, NaturalNode) \
       or isinstance(tree, FnNode) or isinstance(tree, ExpNode) \
       or isinstance(tree, AddNode) or isinstance(tree, SubNode) \
       or isinstance(tree, MulNode) or isinstance(tree, DivNode) \
       or isinstance(tree, IntersectNode) or isinstance(tree, UnionNode) \
       or isinstance(tree, DiffNode):
        return True
    else:
        return True

def trees_unify(tree1, tree2, assigned=[]):
    assign = deepcopy(assigned) # default params are mutable
    if (isinstance(tree1, VarNode) or isinstance(tree1, FnNode)) \
           and tree1.is_metavar:
        if is_expression(tree2):
            assign.append((tree1, tree2))
        else:
            return False, []
    elif (isinstance(tree2, VarNode) or isinstance(tree2, FnNode)) \
           and tree2.is_metavar:
        if is_expression(tree1):
            assign.append((tree2, tree1))
        else:
            return False, []
    elif isinstance(tree1, VarNode) or isinstance(tree2, VarNode):
        if not isinstance(tree1, VarNode) or not isinstance(tree2, VarNode):
            return False, []
        if tree1.name != tree2.name: # if not metavars check names
            return False, []
    elif isinstance(tree1, FnNode) and isinstance(tree2, FnNode):
        if tree1.name != tree2.name: # if not metavars check names
            return False, []
        for i in range(0, len(tree1.args)):
            unified, assign = trees_unify(tree1.args[i], tree2.args[i])
            if not unified:
                return False, []
    else: # we didn't hit a variable, or a pair of functions
        if type(tree1) != type(tree2):
            return False, []
        elif isinstance(tree1, SymbolNode):
            if tree1.name != tree2.name:
                return False, []
        elif isinstance(tree1, TupleNode):
            if len(tree1.args) != len(tree2.args):
                return False, []
            for i in range(0, len(tree1.args)):
                unified, assign = trees_unify(tree1.args[i], tree2.args[i], assign)
                if not unified:
                    return False, []
        elif isinstance(tree1, LRNode):
            unified, assign = trees_unify(tree1.left, tree2.left, assign)
            if not unified:
                return False, []
            unified, assign = trees_unify(tree1.right, tree2.right, assign)
            if not unified:
                return False, []
    # if any case falls through, unification occurred successfully
    return True, assign

def unify(tree1, tree2, assigned=[]):
    assign = deepcopy(assigned) # default params are mutable
    unified, assign = trees_unify(tree1, tree2, assign)
    if not unified:
        return False, []
    i = 0
    while i < len(assign):
        for j in range(0, i):
            assign[j] = make_substitution(assign[j], assign[i])
        j = i + 1
        while j < len(assign):
            if assign[i][0].name == assign[j][0].name:
                unified, assign = trees_unify(assign[i][1], assign[j][1], assign)
                if not unified:
                    return False, []
                del assign[j]
            else:
                assign[j] = make_substitution(assign[j], assign[i])
                j += 1
        i += 1
    return True, assign

def subst(tree1, var, tree2):
    if tree1 == None:
        return tree1
    if isinstance(tree1, VarNode):
        if tree1.name == var.name:
            return deepcopy(tree2)
        else:
            return tree1
    elif isinstance(tree1, FnNode):
        args = [subst(t, var, tree2) for t in tree1.args]
        return FnNode(tree1.name, args)
    elif isinstance(tree1, LRNode):
        tree1.left = subst(tree1.left, var, tree2)
        tree1.right = subst(tree1.right, var, tree2)
        return tree1 
    else:
        return tree1

def make_substitution(assign1, assign2):
    (var1, expr1) = assign1
    (var2, expr2) = assign2

    return (var1, subst(deepcopy(expr1), var2, expr2))