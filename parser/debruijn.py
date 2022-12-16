from parser.ast import *

# TODO: install Python 3.10 manually (sigh!) and switch to structural pattern matching

def annotate_debruijn(tree, ddict, dbr):
    if type(tree) == ExistsNode or type(tree) == ForallNode:
        tree.var.dbr = dbr
        ddict[tree.var.name] = dbr
        annotate_debruijn(tree.expr, dbr + 1, ddict)
    elif type(tree) == VarNode:
        if tree.name in ddict:
            tree.dbr = ddict[tree.name]
    elif type(tree) == ConstNode or type(tree) == VarNode or type(tree) == DepNode:
        pass
    elif type(tree) == FnNode:
        if tree.name in ddict:
            tree.dbr = ddict[tree.name]
    elif type(tree) == NegNode or type(tree) == ParenNode:
        annotate_debruijn(tree.expr, dbr, ddict)
    elif type(tree) == LRNode:
        annotate_debruijn(tree.left, dbr, ddict)
        annotate_debruijn(tree.right, dbr, ddict)
