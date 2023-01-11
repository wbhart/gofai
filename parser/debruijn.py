from parser.ast import *

# TODO: install Python 3.10 manually (sigh!) and switch to structural pattern matching

def annotate_debruijn(tree, dbr=[]):
    if type(tree) == ExistsNode or type(tree) == ForallNode:
        dbr.append(tree.var)
        annotate_debruijn(tree.expr, dbr)
        dbr.pop()
    elif type(tree) == VarNode or type(tree) == FnNode:
        tree.dbr = 0
        if len(dbr) == 0:
            return
        n = len(dbr)
        for i in range(0, n):
            if tree.name == dbr[n - i - 1].name:
                tree.dbr = i + 1
                break
    elif type(tree) == ConstNode or type(tree) == VarNode or type(tree) == DepNode:
        pass
    elif type(tree) == NegNode or type(tree) == ParenNode:
        annotate_debruijn(tree.expr, dbr)
    elif type(tree) == LRNode:
        annotate_debruijn(tree.left, dbr)
        annotate_debruijn(tree.right, dbr)
