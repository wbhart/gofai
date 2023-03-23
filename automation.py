from nodes import ConstNode, AddNode, SubNode, MulNode, EqNode, \
                  BoolNode, ImpliesNode, FnNode, NegNode, ExistsNode, \
                  ForallNode, LRNode

from functools import reduce
from operator import add

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
        # rank moves
        done = execute_move(screen, tl, moves1, moves2)
        if not done:
            screen.stdscr.getkey()

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
        elif isinstance(node, NegNode):
            traverse(node.expr)
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

