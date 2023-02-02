from parser.debruijn import annotate_debruijn
from parser.ast import *
from interface.console import exit_console
import copy

# TODO: implement trees_match for TypeNode and DepNode
# TODO: make functions correctly handle FnNode as a variable like VarNode (FOL vs SOL)
# TODO: make expressions_unify handle set expressions and other unhandled cases

def isexpression(tree, simple=False, top=True):
    """Return True if tree is an expression. A simple expression does not
       contain bound variables, unless it is one. The top parameter is
       is set to False if the function recursively calls itself, so that the
       function can detect when it is at the top level of the tree.
    """
    if isinstance(tree, VarNode):
        if simple:
            return False if tree.dbr > 0 and top == False else True
        else:
            return True
    elif isinstance(tree, ConstNode):
        return True
    elif isinstance(tree, FnNode):
        for t in tree.args:
            if not isexpression(t, simple=simple, top=False):
                return False
        return True
    elif isinstance(tree, NegNode):
        return isexpression(tree.expr, simple=simple, top=False)
    elif isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
        False
    elif isinstance(tree, ExpNode) or isinstance(tree, AddNode) or isinstance(tree, SubNode):
        return isexpression(tree.left, simple=simple, top=False) and isexpression(tree.right, simple=simple, top=False)
    elif isinstance(tree, MulNode) or isinstance(tree, DivNode) or isinstance(tree, IntersectNode):
        return isexpression(tree.left, simple=simple, top=False) and isexpression(tree.right, simple=simple, top=False)
    elif isinstance(tree, UnionNode):
        return isexpression(tree.left, simple=simple, top=False) and isexpression(tree.right, simple=simple, top=False)
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
    elif isinstance(tree, NegNode):
        tree.expr = tree_subst(tree.expr, assign)
        return tree
    else:
        return tree # nothing to substitute

def tree_to_hypothesis(pad, line, tree):
    """Convert the given tree into the tuple (str, tree) where str is the
       string form of the tree. Set the given line of the pad to this tuple.
    """
    annotate_debruijn(tree)
    pad[line] = str(tree), tree

def var_is_assigned_L(assign, tree1):
    """Given a list of assignments [(x, a), (b, y), ....] and a variable
       x check the list for an assignment of the form (x, a) and if one is
       found, return (True, a), otherwise return False, None
    """
    for (a, b) in assign:
        if isinstance(a, VarNode) and a.dbr > 0 and a.name == tree1.name:
            return True, b
    return False, None

def var_is_assigned_R(assign, tree2):
    """Given a list of assignments [(x, b), (a, y), ....] and a variable
       y check the list for an assignment of the form (a, y) and if one is
       found, return (True, a), otherwise return False, None
    """
    for (a, b) in assign:
        if isinstance(b, VarNode) and b.dbr > 0 and b.name == tree2.name:
            return True, a
    return False, None

def flatten_additive(tree, neg=False):
    """Take an additive expression (involving + and -) and return a pair of
       lists (A, S) where A is a list of expressions added together and S is a
       list of expressions subtracted from the former. For example, an
       expression (a - y*z - (b - 2*z)) would return ([a, 2*z], [y*z, b]).
    """
    if isinstance(tree, AddNode):
        a1, s1 = flatten_additive(tree.left, neg)
        a2, s2 = flatten_additive(tree.right, neg)
        return a1 + a2, s1 + s2 # concatenate lists
    elif isinstance(tree, SubNode):
        a1, s1 = flatten_additive(tree.left, neg)
        a2, s2 = flatten_additive(tree.right, not neg)
        return a1 + a2, s1 + s2 # concatenate lists
    else: # We are down to an expression which is not additive, so return it
        if neg == False:
            return [tree], []
        else:
            return [], [tree] 

def flatten_multiplicative(tree):
    """Given an expression involving multiple multiplications, return a list
       of the individual expression multiplied, e.g. 2*(x + y)*z^3 would return
       [2, x + y, z^3].
    """
    if isinstance(tree, MulNode):
        m1 = flatten_multiplicative(tree.left)
        m2 = flatten_multiplicative(tree.right)
        return m1 + m2
    else: # We are down to an expression which is not a multiplication, so return it
        return [tree]

def expressions_unify(tree1, tree2, assign=[], simple=False, copy_trees=True):
    """Determine if two expressions unify after algebraic manipulation.
       Currently the only algebraic manipulation done is applying commutativity
       to rearrange expressions involving addition (and subtraction) and
       multiplication. The function allows for bound variables to unify with
       subexpressions of the other expression, but currently assumes that
       unification is unique and only returns one possibility
       If a unification is found, the function returns 
       (True, [(x, a), (b, y), ....]) where the list gives all the assignments
       of bound variables that must be made for the expressions to unify.
       The function should be called with a list, assign, of all assignments
       known to hold so far. Any new assignments are checked against this list
       to ensure assignments are consistent for every occurrence of the bound
       variable in question.
       If the two expressions must unify without bound variables being assigned
       then set simple=True.
       The copy_trees parameter simply ensures the trees input at the top level
       are copied so they can be modified without clobbering the callers trees.
       If no unification is found, (False, []) is returned.
    """
    if copy_trees:  # if at top level, copy callers trees so they are not clobbered
        tree1 = copy.deepcopy(tree1)
        tree2 = copy.deepcopy(tree2)
    # If the expressions are supposed to be simple and one of the expressions is a
    # bound variable, return False
    if simple and ((isinstance(tree1, VarNode) and tree1.dbr > 0) or \
                   (isinstance(tree2, VarNode) and tree2.dbr > 0)):
        return False, []
    # If both expressions are additive
    if (isinstance(tree1, AddNode) or isinstance(tree1, SubNode)) and \
       (isinstance(tree2, AddNode) or isinstance(tree2, SubNode)):
        # Flatten the additive expressions into lists of terms added and subtracted
        a1, s1 = flatten_additive(tree1)
        a2, s2 = flatten_additive(tree2)
        a1rem = [] # This will be a list of terms not unified in a simple way
        while a1: # Try to unify the list of terms added in a simple way
            d = a1.pop()
            unified = False
            for i in range(0, len(a2)): # check against every term added in the second tree
                unified, ass = expressions_unify(d, a2[i], assign=assign, simple=True, copy_trees=False)
                if unified: # if unified as simple expressions, throw away the terms we unified
                    del a2[i]
                    break
            if not unified: # if the term doesn't unify against any term added in the other tree
                a1rem.append(d) # put it in our list of leftovers
        a1 = a1rem # set a1 back to the list of leftovers
        if simple: # if we are doing a simple unification and we have leftovers
            if a1 or a2:
                return False, []
        else: # now do complex unification
            if len(a1) != len(a2) or len(a1) > 1: # at this point we only allow one unified term
                return False, []
            if a1: # try doing a non-simple unification
                unified, assign = expressions_unify(a1[0], a2[0], assign=assign, simple=False, copy_trees=False)
                if not unified: # if still not unified, return False
                    return False, []
        # Now do the exact same process as above for the terms subtracted on both sides.
        s1rem = []
        while s1:
            d = s1.pop()
            unified = False
            for i in range(0, len(s2)):
                unified, ass = expressions_unify(d, s2[i], assign=assign, simple=True, copy_trees=False)
                if unified:
                    del s2[i]
                    break
            if not unified:
                s1rem.append(d)
        s1 = s1rem
        if simple:
            if s1 or s2:
                return False, []
        else:
            if len(s1) != len(s2) or len(s1) > 1:
                return False, []
            if s1:
                unified, assign = expressions_unify(s1[0], s2[0], assign=assign, simple=False, copy_tree=False)
                if not unified:
                    return False, []
        # if we didn't already return, everything unified and we return the assignments
        return True, assign
    # The same proceduce is carried out for multiplication
    elif isinstance(tree1, MulNode) and isinstance(tree2, MulNode):
        m1 = flatten_multiplicative(tree1) # flatten multiplicative expressions into lists of factors
        m2 = flatten_multiplicative(tree2)
        # As above for the addition case, we first try a simple unification
        m1rem = []
        while m1:
            d = m1.pop()
            unified = False
            for i in range(0, len(m2)):
                unified, ass = expressions_unify(d, m2[i], assign=assign, simple=True, copy_tree=False)
                if unified:
                    del m2[i]
                    break
            if not unified:
                m1rem.append(d)
        m1 = m1rem
        # if we are doing a simple unification and have leftovers, return False
        if simple:
            if m1 or m2:
                return False, []
        else: # we are doing a non-simple unification
            if len(m1) != len(m2) or len(m1) > 1:
                return False, []
            if m1:
                unified, assign = expressions_unify(m1[0], m2[0], assign=assign, simple=False, copy_trees=False)
                if not unified:
                    return False, []
        # if we didn't return already everything unified, return True and the list of assignments
        return true, assign
    # If the left expression is a bound variable
    elif isinstance(tree1, VarNode) and tree1.dbr > 0:
        assigned, a = var_is_assigned_R(assign, tree2) # check if it is already assigned
        if assigned: # if we already assigned this variable
            same, _ = expressions_unify(a, tree1, assign, simple=True, copy_trees=False) # check we assigned it to the same thing
            if not same:
                return False, []
        else:
            assign.append((tree1, tree2)) # if not assigned, assign it
    # if right expression is a bound variable
    elif isinstance(tree2, VarNode) and tree2.dbr > 0:
        assigned, a = var_is_assigned_L(assign, tree1) # check if it is already assigned
        if assigned: # if we already assigned this variable
            same, _ = expressions_unify(a, tree2, assign, simple=True, copy_trees=False) # check we assigned it to the same thing
            if not same:
                return False, []
        else:
            assign.append((tree1, tree2)) # if not assigned, assign it
    # if both expressions are constants, check they are the same
    elif isinstance(tree1, ConstNode) and isinstance(tree2, ConstNode):
        if tree1.value == tree2.value:
            return True, assign
        else:
            return False, []
    # if both expressions are variables which are not bound
    elif isinstance(tree1, VarNode) and isinstance(tree2, VarNode):
        if tree1.name == tree2.name: # check they are the same
            return True, assign
        else:
            return False, []
    # if both expressions are exponentiations
    elif isinstance(tree1, ExpNode) and isinstance(tree2, ExpNode):
       # check left sides unify
       unified, assign = expressions_unify(tree1.left, tree2.left, assign=assign, simple=simple, copy_tree=False)
       if not unified:
           return False, []
       # check right sides unify
       unified, assign = expressions_unify(tree1.right, tree2.right, assign=assign, simple=simple, copy_trees=False)
       if not unified:
           return False, []
       return True, assign
    else:
       raise Exception("Expressions not handled by unify_expressions yet")
                
def trees_unify(tree1, tree2, assign=[]):
    """Unify two trees by finding values for the bound variables that result in
       both statements being the same. The function returns a tuple of the form
       (True, [(x, a), (b, y),... ]) if the trees can be unified, where x = a,
       y = b are the assignments that make the trees match. If the trees cannot
       be unified (False, []) is returned. If assign is set it contains all
       assignments known to hold up to this point.
       If in the process of unifying, two expressions are compared which match
       after some algebraic manipulation, this manipulation is done so the
       unification can succeed. It is the job of the expressions_unify function
       to perform this check.
    """
    while isinstance(tree1, ExistsNode) or isinstance(tree1, ForallNode):
        tree1 = tree1.expr
    while isinstance(tree2, ExistsNode) or isinstance(tree2, ForallNode):
        tree2 = tree2.expr
    if isinstance(tree1, VarNode) and tree1.dbr > 0: # bound variable
        if isexpression(tree2, simple=True):
            assigned, a = var_is_assigned_L(assign, tree1)
            if assigned: # if we already assigned this variable
                unified, assign = expressions_unify(a, tree2, assign) # check we assigned it to the same thing
                if not unified:
                    return False, []
            else:
                assign.append((tree1, tree2)) # if not assigned, assign it
        else:
            return False, []
    elif isinstance(tree2, VarNode) and tree2.dbr > 0: # bound variable
        if isexpression(tree1):
            assigned, a = var_is_assigned_R(assign, tree2)
            if assigned: # if we already assigned this variable
                unified, assign = expressions_unify(a, tree1, assign) # check we assigned it to the same thing
                if not unified:
                    return False, []
            else:
                assign.append((tree1, tree2)) # if not assigned, assign it
        else:
            return False, []
    elif isinstance(tree1, VarNode) or isinstance(tree2, VarNode):
        if tree1.name != tree2.name: # if not bound make sure it matches
            return False, []
    # if trees are expressions, they may not unify without algebraic manipulation
    elif isexpression(tree1) and isexpression(tree2):
        unified, assign = expressions_unify(tree1, tree2, assign) # check if they unify with manipulation
        if not unified:
            return False, []
        else:
            return True, assign
    else: # we didn't hit a variable or expressions, just try to unify without manipulation
        if type(tree1) != type(tree2):
            return False, []
        elif isinstance(tree1, LRNode):
            unify, assign = trees_unify(tree1.left, tree2.left, assign)
            if not unify:
                return False, []
            unify, assign = trees_unify(tree1.right, tree2.right, assign)
            if not unify:
                return False, []
    # if any case falls through, unification occurred successfully
    return True, assign      
  
