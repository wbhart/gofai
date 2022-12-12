class VarNode:
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

class ConstNode:
    def __init__(self, string):
        self.value = int(string)

    def __str__(self):
        return str(self.value)

class ExpNode:
    def __init__(self, base, exp):
        self.base = base
        self.exp = exp

    def __str__(self):
        return str(self.base)+"^"+str(self.exp)

class FnNode:
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self):
        return self.name+"("+', '.join(str(e) for e in self.args)+")"

class AddNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" + "+str(self.right)

class SubNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" - "+str(self.right)

class MulNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"*"+str(self.right)

class DivNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"/"+str(self.right)

class LtNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" < "+str(self.right)

class GtNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" > "+str(self.right)

class LeqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\leq "+str(self.right)

class GeqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\geq "+str(self.right)

class EqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" = "+str(self.right)

class NeqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\neq "+str(self.right)

class ImpliesNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\implies "+str(self.right)

class IffNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\leftrightarrow "+str(self.right)

class AndNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\\wedge"+str(self.right)

class OrNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\\vee"+str(self.right)

class IntersectNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\\cap"+str(self.right)

class UnionNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\\cup"+str(self.right)

class SubsetNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\subset "+str(self.right)

class SubseteqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\subseteq "+str(self.right)

class SupsetNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\supset "+str(self.right)

class SupseteqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\supseteq "+str(self.right)

class DiffNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\setminus "+str(self.right)

class NegNode:
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return "\\neg"+str(self.right)

class ExistsNode:
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr

    def __str__(self):
        return "\\exists "+str(self.var)+" "+str(self.expr)

class ForallNode:
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr

    def __str__(self):
        return "\\forall "+str(self.var)+" "+str(self.expr)

class ElemNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\in "+str(self.right)

class TypeNode:
    def __init__(self, var, typename):
        self.var = var
        self.typename = typename

    def __str__(self):
        return str(self.var)+" : "+str(self.typename)

class DepNode:
    def __init__(self, typename, dep):
        self.typename = typename
        self.dep = dep

    def __str__(self):
        return str(self.typename)+"("+str(dep)+")"

class ParenNode:
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return "("+str(self.expr)+")"

