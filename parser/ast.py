class VarNode:
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

class ConstNode:
    def __init__(self, string):
        self.value = int(string)

    def __str__(self):
        return str(self.value)

    def __repr__(self):
        return str(self.value)

class ExpNode:
    def __init__(self, base, exp):
        self.base = base
        self.exp = exp

    def __str__(self):
        return str(self.base)+"^"+str(self.exp)

    def __repr__(self):
        return repr(self.base)+"^"+repr(self.exp)

class FnNode:
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self):
        return self.name+"("+', '.join(str(e) for e in self.args)+")"

    def __repr__(self):
        return self.name+"("+', '.join(repr(e) for e in self.args)+")"

class AddNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" + "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" + "+repr(self.right)

class SubNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" - "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" - "+repr(self.right)

class MulNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"*"+str(self.right)

    def __repr__(self):
        return repr(self.left)+"*"+repr(self.right)

class DivNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"/"+str(self.right)

    def __repr__(self):
        return repr(self.left)+"/"+repr(self.right)

class LtNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" < "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" < "+repr(self.right)

class GtNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" > "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" > "+repr(self.right)

class LeqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2264 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\leq "+repr(self.right)

class GeqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2265 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\geq "+repr(self.right)

class EqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" = "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" = "+repr(self.right)

class NeqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2260 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\neq "+repr(self.right)

class ImpliesNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u21d2 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\implies "+repr(self.right)

class IffNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u21d4 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\leftrightarrow "+repr(self.right)

class AndNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\u2227"+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\wedge "+repr(self.right)

class OrNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\u2228"+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\vee "+repr(self.right)

class IntersectNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\u2229"+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\cap "+repr(self.right)

class UnionNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+"\u222a"+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\cup "+repr(self.right)

class SubsetNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2282 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\subset "+repr(self.right)

class SubseteqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2286 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\subseteq "+repr(self.right)

class SupsetNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2283 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\supset "+repr(self.right)

class SupseteqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2287 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\supseteq "+repr(self.right)

class DiffNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \\ "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\setminus "+repr(self.right)

class NegNode:
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return "\u00ac"+str(self.right)

    def __repr__(self):
        return "\\neg"+repr(self.right)

class ExistsNode:
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr

    def __str__(self):
        return "\u2203"+str(self.var)+" "+str(self.expr)

    def __repr__(self):
        return "\\exists "+repr(self.var)+" "+repr(self.expr)

class ForallNode:
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr

    def __str__(self):
        return "\u2200"+str(self.var)+" "+str(self.expr)

    def __repr__(self):
        return "\\forall "+repr(self.var)+" "+repr(self.expr)

class ElemNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left)+" \u2208 "+str(self.right)

    def __repr__(self):
        return repr(self.left)+" \\in "+repr(self.right)

class TypeNode:
    def __init__(self, var, typename):
        self.var = var
        self.typename = typename

    def __str__(self):
        return str(self.var)+" : "+str(self.typename)

    def __repr__(self):
        return repr(self.var)+" : "+repr(self.typename)

class DepNode:
    def __init__(self, typename, dep):
        self.typename = typename
        self.dep = dep

    def __str__(self):
        return str(self.typename)+"("+str(dep)+")"

    def __repr__(self):
        return repr(self.typename)+"("+repr(dep)+")"

class ParenNode:
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        return "("+str(self.expr)+")"

    def __repr__(self):
        return "("+repr(self.expr)+")"
