from parser.debruijn import annotate_debruijn
from parser.ast import *

# TODO: implement trees_match for TypeNode and DepNode
# TODO: make tree_is_Px correctly handle FnNode as a variable like VarNode

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

def rotate_nodes(tree, num):
    """Rotate the first num nodes of the given tree.
    """
    if num != 1:
        node = tree
        t = tree
        tree = tree.expr
        for i in range(0, num - 1):
            t = t.expr
        node.expr = t.expr
        t.expr = node
    return tree

def tree_is_Px_recurse(tree, P, Qx, a=None, dbr=[]):
    """Return (True, a) if the given tree is of the form P(x) where x is the
       bound variable in P with the quantifier Qx and where a is an expression
       such that tree = P(a). Otherwise return (False, None). If the optional
       argument a is provided the function checks that tree = P(a) for that
       specific value of a and returns (False, None) if not. If dbr is set it
       is a list of the qunatifiers in scope at this level of the tree.
    """
    if isinstance(P, ForallNode):
        num_forall_P = 0
        t = P
        while isinstance(t, ForallNode):
            num_forall_P += 1
            t = t.expr
        num_forall_tree = 0
        t = tree
        while isinstance(t, ForallNode):
            num_forall_tree += 1
            t = t.expr
        if num_forall_P != num_forall_tree:
            return False, None
        matched = False
        for i in range(0, num_forall_t):
            tree = rotate_nodes(tree, num_forall_tree)
            annotate_debruijn(tree, dbr)
            if not Matched:
                push(dbr, tree.var)
                is_Px, expr = tree_is_Px_recurse(tree.expr, P.expr, Qx, a, dbr)
                if is_Px:
                    a = expr
                    matched = True
                pop(dbr)
        return matched, a
    elif isinstance(P, ExistsNode):
        num_exists_P = 0
        t = P
        while isinstance(t, ExistsNode):
            num_exists_P += 1
            t = t.expr
        num_exists_tree = 0
        t = tree
        while isinstance(t, ExistsNode):
            num_exists_tree += 1
            t = t.expr
        if num_exists_P != num_exists_tree:
            return False, None
        matched = False
        for i in range(0, num_exists_t):
            tree = rotate_nodes(tree, num_exists_tree)
            annotate_debruijn(tree, dbr)
            if not Matched:
                push(dbr, tree.var)
                is_Px, expr = tree_is_Px_recurse(tree.expr, P.expr, Qx, a, dbr)
                if is_Px:
                    a = expr
                    matched = True
                pop(dbr)
        return matched, a
    elif isinstance(P, VarNode):
        if P.name == x.name: # we found x
            if not isexpression(tree):
                return False, None
            elif a != None:
                if trees_match(a, tree):
                    return True, a
                else:
                    return False, None
            else:
                return True, a
        elif not isinstance(tree, VarNode):
            return False, None
        elif P.dbr > 0:
            if tree.dbr != P.dbr:
                return False, None
        elif tree.name != P.name:
            return False, None
        return True, a
    elif isinstance(P, LRNode) or isinstance(P, ExpNode):
        if not isinstance(tree, type(P)):
            return False, None
        is_Px, expr = tree_is_Px_recurse(tree.left, P.left, Qx, a, dbr)
        if is_Px:
            a = expr
        else:
            return False, None
        is_Px, expr = tree_is_Px_recurse(tree.right, P.right, Qx, a, dbr)
        if is_Px:
            a = expr
        else:
            return False, None
        return True, a
    elif isinstance(P, ConstNode):
        if not isinstance(tree, ConstNode):
            return False, None
        elif tree.value != P.value:
            return False, None
        else:
            return True, a
    elif isinstance(P, FnNode):
        if not isinstance(tree, FnNode):
            return False, None
        elif tree.name != P.name or len(tree.args) != len(P.args):
            return False, None
        for i in range(0, len(tree.args)):
            is_Px, expr = tree_is_Px_recurse(tree.args[i], P.args[i], Qx, a, dbr)
            if is_Px:
                a = expr
            else:
                return False, None
        return True, a
    elif isinstance(P, NegNode) or isinstance(P, ParenNode):
        if not isinstance(tree, type(P)):
            return False, None
        is_Px, expr = tree_is_Px_recurse(tree.expr, P.expr, Qx, a, dbr)
        if is_Px:
            a = expr
        else:
            return False, None
        return True, a

def tree_is_Px(tree, Q):
    """Return (True, a, n) if tree is of the form P(a) where Q = R x P(x) for
       some quantifier R (one of the first commuting ones), and n is which
       quantifier is R, numbered starting from 0 on the left of Q.
    """
    a = None
    n = 0
    if isinstance(Q, ForallNode):
        num_forall_Q = 0
        t = Q
        while isinstance(t, ForallNode):
            num_forall_Q += 1
            t = t.expr
        for i in range(0, num_forall_Q):
            Q = rotate_nodes(Q, num_forall_Q)
            annotate_debruijn(Q, [])
            if not Matched:
                n += 1
                is_Px, expr = tree_is_Px_recurse(tree.expr, Q.expr, Q.var, a)
                if is_Px:
                    a = expr
                    matched = True
        return matched, a, n%num_forall_Q
    elif isinstance(Q, ExistsNode):
        num_exists_Q = 0
        t = Q
        while isinstance(t, ExistsNode):
            num_exists_Q += 1
            t = t.expr
        for i in range(0, num_exists_Q):
            Q = rotate_nodes(Q, num_exists_Q)
            annotate_debruijn(Q, [])
            if not Matched:
                n += 1
                is_Px, expr = tree_is_Px_recurse(tree.expr, Q.expr, Q.var, a)
                if is_Px:
                    a = expr
                    matched = True
        return matched, a, n%num_exists_Q
    else:
        return False, None

def tree_to_hypothesis(pad, line, tree):
    """Convert the given tree into the tuple (str, tree) where str is the
       string form of the tree. Set the given line of the pad to this tuple.
    """
    annotate_debruijn(tree)
    pad[line] = str(tree), tree

def trees_match(tree1, tree2):
    """Return True if the given trees are the same expression, up to names of
       bound variables. Does not permute deBruijn indices.
    """
    if type(tree1) != type(tree2):
        return False
    if isinstance(tree1, LRNode) or isinstance(tree1, ExpNode):
        return trees_match(tree1.left, tree2.left) and trees_match(tree1.right, tree2.right)
    elif isinstance(tree1, VarNode):
        if tree1.dbr > 0:
            return tree2.dbr == tree1.dbr
        else:
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
        
