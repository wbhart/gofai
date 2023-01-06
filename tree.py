from parser.debruijn import annotate_debruijn
from parser.ast import *

# TODO: implement trees_match for TypeNode and DepNode

def tree_to_hypothesis(pad, line, tree):
    ddict = dict()
    annotate_debruijn(tree, ddict, 0)
    pad[line] = str(tree), tree, ddict

def trees_match(tree1, tree2):
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
        
