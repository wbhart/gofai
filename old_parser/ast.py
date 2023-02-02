def isatomic(node):
    if isinstance(node, LRNode):
        return False
    elif isinstance(node, ExistsNode) or isinstance(node, ForallNode):
        return False

# Common class for all nodes with a left and right child
class LRNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def paren_str(self, child):
        if not isatomic(child) and precedence[type(child)] > precedence[type(self)]:
            return '('+str(child)+')'
        else:
            return str(child)

    def paren_repr(self, child):
        if not isatomic(child) and precedence[type(child)] > precedence[type(self)]:
            return '('+repr(child)+')'
        else:
            return repr(child)

# AST Nodes
class VarNode:
    def __init__(self, name):
        self.name = name
        self.dbr = -1 # used for debruijn indices (-1 = not set)

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

class ExpNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"^"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+"^"+self.paren_repr(self.right)

class FnNode:
    def __init__(self, name, args):
        self.name = name
        self.args = args
        self.dbr = -1 # debruijn indices (-1 = not set)

    def __str__(self):
        return self.name+"("+', '.join(str(e) for e in self.args)+")"

    def __repr__(self):
        return self.name+"("+', '.join(repr(e) for e in self.args)+")"

class AddNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" + "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" + "+self.paren_repr(self.right)

class SubNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" - "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" - "+self.paren_repr(self.right)

class MulNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"*"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+"*"+self.paren_repr(self.right)

class DivNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"/"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+"/"+self.paren_repr(self.right)

class LtNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" < "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" < "+self.paren_repr(self.right)

class GtNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" > "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" > "+self.paren_repr(self.right)

class LeqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2264 "+paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\leq "+self.paren_repr(self.right)

class GeqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2265 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\geq "+self.paren_repr(self.right)

class EqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" = "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" = "+self.paren_repr(self.right)

class NeqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2260 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\neq "+self.paren_repr(self.right)

class ImpliesNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u21d2 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\implies "+self.paren_repr(self.right)

class IffNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u21d4 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\leftrightarrow "+self.paren_repr(self.right)

class AndNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"\u2227"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\wedge "+self.paren_repr(self.right)

class OrNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"\u2228"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\vee "+self.paren_repr(self.right)

class IntersectNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"\u2229"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\cap "+self.paren_repr(self.right)

class UnionNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"\u222a"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\cup "+self.paren_repr(self.right)

class SubsetNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2282 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\subset "+self.paren_repr(self.right)

class SubseteqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2286 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\subseteq "+self.paren_repr(self.right)

class SupsetNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2283 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\supset "+self.paren_repr(self.right)

class SupseteqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2287 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\supseteq "+self.paren_repr(self.right)

class DiffNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \\ "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\setminus "+self.paren_repr(self.right)

class NegNode:
    def __init__(self, expr):
        self.expr = expr

    def __str__(self):
        if not atomic(self.expr) and precedence[type(self.expr)] > precedence[type(self)]:
            return "\u00ac"+'('+str(self.expr)+')'
        else:
            return "\u00ac"+str(self.expr)

    def __repr__(self):
        if not atomic(self.expr) and precedence[type(self.expr)] > precedence[type(self)]:
            return "\\neg"+'('+repr(self.expr)+')'
        else:
            return "\\neg"+repr(self.expr)

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

class ElemNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2208 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\in "+self.paren_repr(self.right)

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
        return str(self.typename)+"("+str(self.dep)+")"

    def __repr__(self):
        return repr(self.typename)+"("+repr(self.dep)+")"

precedence = {ExistsNode:8, ForallNode:8,
              ImpliesNode:7, IffNode:7,
              AndNode:6, OrNode:6,
              # Set nodes
              SubsetNode:5, SubseteqNode:5,
              SupsetNode:5, SupseteqNode:5, ElemNode:5,
              DiffNode:4,
              UnionNode:3, IntersectNode:3,
              # Arithmetic nodes
              LeqNode:5, LtNode:5,
              GeqNode:5, GtNode:5,
              EqNode:5, NeqNode:5,
              AddNode:4, SubNode:4,
              NegNode:3,
              MulNode:2, DivNode:2,
              ExpNode:1,
              ConstNode:0, VarNode:0, FnNode:0}
