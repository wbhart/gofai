from nodes import ConstNode, AddNode, SubNode, MulNode, EqNode, \
                  BoolNode, ImpliesNode, FnNode, ExistsNode, \
                  ForallNode, VarNode, LRNode

from functools import reduce
from operator import add
import copy

var_names = {'Natural' : ['m', 'n', 'p', 'q', 'a', 'b', 'c', 'd', \
                         'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'], \
             'Integer' : ['m', 'n', 'p', 'q', 'a', 'b', 'c', 'd', \
                         'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'], \
             'Real' : ['x', 'y', 'z', 'w', 'a', 'b', 'c', 'd', 'r', \
                       's', 't', 'u', 'v'], \
             'Complex' : ['z', 'u', 'v', 'w', 'c', 'd', 'r', 's', 't']}

def addition(tree):
   sum = tree.left.value + tree.right.value
   return ConstNode(sum)

def subtraction(tree):
    diff = tree.left.value - tree.right.value
    return ConstNode(diff)

def multiplication(tree):
    prod = tree.left.value*tree.right.value
    return ConstNode(prod)

def equality(tree):
    val = tree.left.value == tree.right.value
    return BoolNode(val)

class Transform:
    def __init__(self, name, transform):
        self.name = name
        self.transform = transform

class AutoDict:
    def __init__(self):
        self.dict = dict()
        self.dict[ihash(add_hash('Const', '+', 'Const'))] = \
            [('Natural + Natural', Transform('addition', addition))]
        self.dict[ihash(add_hash('Const', '-', 'Const'))] = \
            [('Natural - Natural', Transform('subtraction', subtraction))]
        self.dict[ihash(add_hash('Const', '*', 'Const'))] = \
            [('Natural * Natural', Transform('multiplication', multiplication))]
        self.dict[ihash(add_hash('Const', '=', 'Const'))] = \
            [('Natural = Natural', Transform('equality', equality))]

    def __getitem__(self, key):
        if key in self.dict:
            return self.dict[key]
        else:
            return []

    def __setitem__(self, key, value):
        if key in self.dict:
            vallist = self.dict[key]
            vallist.append(value)
        else:
            self.dict[key] = [value]
       
def iarr(string):
    return list(map(ord, list(string)))

def add_hash(*args):
    n = max(map(len, args))
    h = list(map(sum, map(lambda x : iarr(x)+(n - len(x))*[0], args)))
    return h

def add_iarr(*args):
    n = max(map(len, args))
    h = list(map(sum, map(lambda x : x +(n - len(x))*[0], args)))
    return h

def ihash(arr):
    return reduce(add, map(str, arr))

def automate(screen, tl, ad):
    done = False
    while not done:
        moves1 = []
        moves2 = []
        for tree in tl.tlist1.data:
            move = []
            identify_moves(tree, ad, move)
            moves1.append(move)
        for tree in tl.tlist2.data:
            move = []
            identify_moves(tree, ad, move)
            moves2.append(move)
        # join hypotheses and targets into single tree temporarily
        data = join_problem_state(tl.tlist1.data, tl.tlist2.data)
        comsub = find_common_subexpressions(data)
        conj = conjecture_theorems(data, comsub)
        # rank moves
        done = execute_move(screen, tl, moves1, moves2)
        if not done:
            screen.stdscr.getkey()

def conjecture_theorems(data, comsub):
    if contains_constants(comsub):
        data = copy.deepcopy(data)
        varlist = [n.name for n in get_vars(data)] # get list of current vars used
        binders = [] # any new biders to be added

        def replace_constants(data, cslist, newvar):
            if data in cslist:
                return copy.deepcopy(newvar)
            if isinstance(data, LRNode):
                data.left = replace_constants(data.left, cslist, newvar)
                data.right = replace_constants(data.right, cslist, newvar)
            return data
        
        for nlist in comsub:
            if is_constant_expr(nlist[0]):
                var_type = nlist[0].type
                new_var = get_new_var(var_type, varlist)
                data = replace_constants(data, nlist, new_var)
                new_bind = ForallNode(new_var, None)
                binders.append(new_bind)
        
        # split into hypotheses and targets again
        hyps = data.left
        targs = data.right
        quants = None
        for b in binders:
            in1 = var_in_tree(hyps, b.var)
            in2 = var_in_tree(targs, b.var)
            if in1 and in2:
                b.expr = quants
                quants = b
            elif in1 and not in2:
                b.expr = hyps
                hyps = b
            else:
                b.expr = targs
                targs = b
        return quants, hyps, targs

def var_in_tree(tree, var):
    if isinstance(tree, VarNode):
        return tree.name == var.name
    elif isinstance(tree, LRNode):
        if var_in_tree(tree.left, var):
             return True
        else:
             return var_in_tree(tree.right, var)
    else:
        return False

def first_not_in_second(list1, list2):
    return next(filter(lambda x: x not in list2, list1), None)

def get_new_var(var_type, usedvarlist):
    varlist = var_names[var_type.name]
    return VarNode(first_not_in_second(varlist, usedvarlist))

def get_vars(data):
    varlist = []

    def traverse(data):
        if isinstance(data, VarNode):
            found = False
            for v in varlist:
                if v.name == data.name:
                    found = True
            if not found:
                varlist.append(data)
        elif isinstance(data, LRNode):
            traverse(data.left)
            traverse(data.right)
        elif isinstance(data, FnNode):
            for p in data.args:
                traverse(p)
        elif isinstance(data, ExistsNode) or isinstance(data, ForallNode):
            traverse(data.expr)
    
    traverse(data)
    return varlist

def contains_constants(comsub):
    for c in comsub:
        if is_constant_expr(c[0]):
            return True
    return False

def is_constant_expr(c):
    if isinstance(c, ConstNode):
        return True
    elif isinstance(c, AddNode) or isinstance(c, SubNode) or \
       isinstance(c, MulNode) or isinstance(c, DivNode) or \
       isinstance(c, ExpNode):
        return is_constant_expr(c.left) and is_constant_expr(c.right)
    elif isinstance(c, FnNode):
        for p in c.args:
            if not is_constant_expr(p):
                return False
        return True
    else:
        return False 

def identify_moves(tree, ad, moves):
    ty = get_typed(tree)
    if isinstance(tree, LRNode):
        iarr1 = identify_moves(tree.left, ad, moves)
        iarr2 = identify_moves(tree.right, ad, moves)
        if isinstance(tree, AddNode):
            iar = add_iarr(iarr1, iarr('+'), iarr2)
        elif isinstance(tree, SubNode):
            iar = add_iarr(iarr1, iarr('-'), iarr2)
        elif isinstance(tree, MulNode):
            iar = add_iarr(iarr1, iarr('*'), iarr2)
        elif isinstance(tree, EqNode):
            iar = add_iarr(iarr1, iarr('='), iarr2)
        else:
            raise Exception("Node not handled")
        h = ihash(iar)
        if h in ad.dict:
            pot = ad[h] # get potential moves
            for p in pot:
                if p[0] == ty:
                    moves.append((tree, p[1]))
        return iar
    elif isinstance(tree, ConstNode):
        return iarr('Const')
    else:
        raise Exception("Node not handled")

def get_typed(tree):
    if isinstance(tree, LRNode):
        ltyped = get_typed(tree.left)
        rtyped = get_typed(tree.right)
        if isinstance(tree, AddNode):
            typed = ltyped+' + '+rtyped
        elif isinstance(tree, SubNode):
            typed = ltyped+' - '+rtyped
        elif isinstance(tree, MulNode):
            typed = ltyped+' * '+rtyped
        elif isinstance(tree, EqNode):
            typed = ltyped+' = '+rtyped
        else:
            raise Exception("Node not handled")
        return typed
    elif isinstance(tree, ConstNode):
        return 'Natural'
    else:
        raise Exception("Node not handled")

def join_problem_state(tl1, tl2):
    if not tl1:
        hyps = BoolNode(True)
    else:
        hyps = tl1[0]
        for i in tl1[1:-1]:
            hyps = AndNode(hyps, i)
    if not tl2:
        tars = BoolNode(True)
    else:
        tars = tl2[0]
        for i in tl2[1:-1]:
            tars = AndNode(tars, i)
    return ImpliesNode(hyps, tars)
        
def execute_move(screen, tl, moves1, moves2):
    for i in range(len(moves1)):
        m = moves1[i]
        if m:
            m = m[0]
            tl.tlist1.data[i] = apply_hyp_move(tl, i, m)
            screen.pad1.pad[i] = str(tl.tlist1.data[i])
            screen.pad1.refresh()
            return False # not done
    for i in range(len(moves2)):
        m = moves2[i]
        if m:
            m = m[0]
            tl.tlist2.data[i] = apply_target_move(tl, i, m)
            screen.pad2.pad[i] = str(tl.tlist2.data[i])
            screen.pad2.refresh()
            return check_if_done(tl)
    return True

def check_if_done(tl):
    for d in tl.tlist2.data:
        if d and not isinstance(d, BoolNode):
            return False
    return True

def apply_hyp_move(t1, i, m):
    return tl

def apply_target_move(tl, i, m):
    target = tl.tlist2.data[i]
    if isinstance(m[1], Transform):
        new_tree = m[1].transform(m[0])
        new_target = replace_node(target, m[0], new_tree)
        return new_target
    else:
        return target

def replace_node(tree, old, new):
    if tree == old:
        return new
    elif isinstance(tree, LRNode):
        if tree.left == old:
            tree.left = new
            return tree
        elif tree.right == old:
            tree.right = new
            return tree
        tree.left = replace_node(tree.left, old, new)
        tree.right = replace_node(tree.right, old, new)
        return tree
    else:
        return tree

def find_common_subexpressions(root):
    subexpr_nodes = {}  # Dictionary to store nodes for each subexpression
    
    def traverse(node):
        if isinstance(node, LRNode):
            # Traverse left and right subtrees
            traverse(node.left)
            traverse(node.right)
        elif isinstance(node, FnNode):
            for n in node.args:
                traverse(n)
        elif isinstance(node, ExistsNode) or isinstance(node, ForallNode):
            traverse(node.var)
            traverse(node.expr)

        # Get current subtree as a string
        subexpr = str(node)
        
        # Add node to the list of nodes corresponding to the subexpression
        if subexpr in subexpr_nodes:
            subexpr_nodes[subexpr].append(node)
        else:
            subexpr_nodes[subexpr] = [node]
        
        return subexpr
    
    traverse(root)
    
    # Extract the subexpression lists containing more than one node
    common_subexprs = [nodes for nodes in subexpr_nodes.values() \
                       if len(nodes) > 1]
    
    return common_subexprs

