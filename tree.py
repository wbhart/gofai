from parser.debruijn import annotate_debruijn
from parser.ast import *
from interface.console import exit_console
import copy

# TODO: implement trees_match for TypeNode and DepNode
# TODO: make tree_is_Px correctly handle FnNode as a variable like VarNode
# TODO: implement version of trees_match that permute quantifiers (optional arg?)
# TODO: make trees_unify handle expressions that are arithmetically equal but not syntactically identical

def isexpression(tree):
    if isinstance(tree, VarNode):
        return True
    elif isinstance(tree, ConstNode):
        return True
    elif isinstance(tree, FnNode):
        return True
    elif isinstance(tree, NegNode):
        return True
    elif isinstance(tree, ParenNode):
        return isexpression(tree.expr)
    elif isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
        False
    elif isinstance(tree, ExpNode) or isinstance(tree, AddNode) or isinstance(tree, SubNode):
        return True
    elif isinstance(tree, MulNode) or isinstance(tree, DivNode) or isinstance(tree, IntersectNode):
        return True
    elif isinstance(tree, UnionNode):
        return True
    else:
        return False

def tree_find_quantifier(tree, var):
    """Given a VarNode var, find the associated quantifier in the given tree
       and return it.
    """
    if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
        if tree.var.name == var.name:
            return tree
        else:
            return tree_find_quantifier(tree.expr, var)
    if isinstance(tree, LRNode):
        if isexpression(tree):
            return None
        else:
            q = tree_find_quantifier(tree.left, var)
            if q != None:
                return q
            return tree_find_quantifier(tree.right, var)
    if isinstance(tree, ParenNode):
        return tree_find_quantifier(tree.expr, var)
    return None

def tree_subst(tree, assign):
    """Given a tree and a list of assignments [(x, a), (y, b), ....] make the
       given substitions in the tree, including possibly changing quantifiers.
    """
    if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
        for (a, b) in assign:
            if a.var.name == tree.var.name:
                if isinstance(b, ForallNode) or isinstance(b, ExistsNode): # if substituting quantifier
                    b.expr = tree_subst(tree.expr, assign)
                    return b
                else: # we are substituting a value, so drop quantifier
                    return tree_subst(tree.expr, assign)
        return tree_subst(tree.expr, assign) # quantifier doesn't need substituting
    elif isinstance(tree, VarNode):
        if tree.dbr > 0: # we have a bound variable
            for (a, b) in assign:
                if a.var.name == tree.name:
                    if isinstance(b, ForallNode) or isinstance(b, ExistsNode): # if substituting variable
                        tree.name = b.var.name
                        return tree
                    else: # we are substituting a value
                        return copy.deepcopy(b)
            return tree # nothing was substituted
        else: # not bound
            return tree
    elif isinstance(tree, LRNode):
        tree.left = tree_subst(tree.left, assign)
        tree.right = tree_subst(tree.right, assign)
        return tree
    elif isinstance(tree, FnNode):
        for i in range(0, len(tree.args)):
            tree.args[i] = tree_subst(tree.args[i], assign)
        return tree
    elif isinstance(tree, ParenNode) or isinstance(tree, NegNode):
        tree.expr = tree_subst(tree.expr, assign)
        return tree
    else:
        return tree # nothing to substitute

def tree_to_hypothesis(pad, line, tree):
    """Convert the given tree into the tuple (str, tree) where str is the
       string form of the tree. Set the given line of the pad to this tuple.
    """
    while isinstance(tree, ParenNode):
        tree = tree.expr
    annotate_debruijn(tree)
    pad[line] = str(tree), tree

def var_is_assigned_L(assign, tree1):
    for (a, b) in assign:
        if isinstance(a, VarNode) and a.dbr > 0 and a.name == tree1.name:
            return True, b
    return False, None

def var_is_assigned_R(assign, tree2):
    for (a, b) in assign:
        if isinstance(b, VarNode) and b.dbr > 0 and b.name == tree2.name:
            return True, a
    return False, None

def trees_unify(tree1, tree2, assign=[]):
    """Unify two trees by finding values for the bound variables that result in
       both statements being the same. The function returns a tuple of the form
       (True, [(x, a), (b, y),... ]) if the trees can be unified, where x = a,
       y = b are the assignments that make the trees match. If the trees cannot
       be unified (False, []) is returned. If assign is set it contains all
       assignments known to hold up to this point.
    """
    while isinstance(tree1, ExistsNode) or isinstance(tree1, ForallNode) or isinstance(tree1, ParenNode):
        tree1 = tree1.expr
    while isinstance(tree2, ExistsNode) or isinstance(tree2, ForallNode) or isinstance(tree2, ParenNode):
        tree2 = tree2.expr
    if isinstance(tree1, VarNode) and tree1.dbr > 0: # bound variable
        if isexpression(tree2):
            assigned, a = var_is_assigned_L(assign, tree1)
            if assigned: # if we already assigned this variable
                if not trees_match(a, tree2): # check we assigned it to the same thing
                    return False, []
            else:
                assign.append((tree1, tree2)) # if not assigned, assign it
        else:
            return False, []
    elif isinstance(tree2, VarNode) and tree2.dbr > 0: # bound variable
        if isexpression(tree1):
            assigned, a = var_is_assigned_R(assign, tree2)
            if assigned: # if we already assigned this variable
                if not trees_match(a, tree1): # check we assigned it to the same thing
                    return False, []
            else:
                assign.append((tree1, tree2)) # if not assigned, assign it
        else:
            return False, []
    elif isinstance(tree1, VarNode) or isinstance(tree2, VarNode):
        if not trees_match(tree1, tree2): # if not bound make sure it matches
            exit_console()
            print(tree1)
            print(tree2)
            print(tree2.dbr)
            exit(1)
            return False, []
    else: # we didn't hit a variable
        if type(tree1) != type(tree2):
            return False, []
        elif isinstance(tree1, ConstNode):
            if tree1.value != tree2.value:
                return False, []
        elif isinstance(tree1, LRNode):
            unify, assign = trees_unify(tree1.left, tree2.left, assign)
            if not unify:
                return False, []
            unify, assign = trees_unify(tree1.right, tree2.right, assign)
            if not unify:
                return False, []
        elif isinstance(tree1, NegNode) or isinstance(tree1, ParenNode):
            unify, assign = trees_unify(tree1.expr, tree2.expr, assign)
            if not unify:
                return False, []
        elif isinstance(tree1, FnNode):
            if tree1.name != tree2.name or len(tree1.args) != len(tree2.args):
                return False, []
            for i in range(0, tree1.args):
                unify, assign = trees_unify(tree1.args[i], tree2.args[i], assign)
                if not unify:
                    return False, []
    return True, assign      
  
def trees_match(tree1, tree2):
    """Return True if the given trees are the same expression, up to names of
       bound variables. Does not permute deBruijn indices.
    """
    if type(tree1) != type(tree2):
        return False
    if isinstance(tree1, LRNode) or isinstance(tree1, ExpNode):
        return trees_match(tree1.left, tree2.left) and trees_match(tree1.right, tree2.right)
    elif isinstance(tree1, VarNode):
        return tree2.name == tree1.name
    elif isinstance(tree1, ConstNode):
        return tree1.value == tree2.value
    elif isinstance(tree1, FnNode):
        if tree1.name != tree2.name or len(tree1.args) != len(tree2.args):
            return False
        for i in range(0, len(tree1.args)):
            if not trees_match(tree1.args[i], tree2.args[i]):
                return False
        return True
    elif isinstance(tree1, NegNode) or isinstance(tree1, ParenNode):
        return trees_match(tree1.expr, tree2.expr)
    elif isinstance(tree1, ExistsNode) or isinstance(tree1, ForallNode):
        return trees_match(tree1.var, tree2.var) and trees_match(tree1.expr, tree2.expr)
        
