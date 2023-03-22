from nodes import ConstNode, AddNode, SubNode, MulNode, EqNode, \
                  BoolNode, LRNode
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
                  [Transform('addition', addition)]
        self.dict[ihash(add_hash('Const', '-', 'Const'))] = \
                  [Transform('subtraction', subtraction)]
        self.dict[ihash(add_hash('Const', '*', 'Const'))] = \
                  [Transform('multiplication', multiplication)]
        self.dict[ihash(add_hash('Const', '=', 'Const'))] = \
                  [Transform('equality', equality)]

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
        # rank moves
        done = execute_move(screen, tl, moves1, moves2)
        if not done:
            screen.stdscr.getkey()

def identify_moves(tree, ad, moves):
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
            moves.append((tree, ad[h][0]))
        return iar
    elif isinstance(tree, ConstNode):
        return iarr('Const')

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
