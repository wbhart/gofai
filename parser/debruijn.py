from parser.ast import *
from interface.console import exit_console

# TODO: install Python 3.10 manually (sigh!) and switch to structural pattern matching

def annotate_debruijn(tree, dbr=[]):
    if isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
        dbr.append(tree.var)
        annotate_debruijn(tree.expr, dbr)
        dbr.pop()
    elif isinstance(tree, VarNode) or isinstance(tree, FnNode):
        tree.dbr = 0
        if len(dbr) == 0:
            return
        n = len(dbr)
        for i in range(0, n):
            if tree.name == dbr[n - i - 1].name:
                tree.dbr = i + 1
                break
    elif isinstance(tree, ConstNode) or isinstance(tree, VarNode) or isinstance(tree, DepNode):
        pass
    elif isinstance(tree, NegNode) or isinstance(tree, ParenNode):
        annotate_debruijn(tree.expr, dbr)
    elif isinstance(tree, LRNode):
        annotate_debruijn(tree.left, dbr)
        annotate_debruijn(tree.right, dbr)
