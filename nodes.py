from sorts import NumberSort, Constraint, Universum, SetSort, TupleSort, PredSort, \
                  FunctionConstraint, univar
from typeclass import OrderedSemiringClass

def isatomic(node):
    if isinstance(node, LRNode):
        return False
    elif isinstance(node, ExistsNode) or isinstance(node, ForallNode):
        return False
    return True

def needs_paren_right(tree, child):
    # Do we need to check
    if isatomic(child):
        return False
    if precedence[type(child)] < precedence[type(tree)]:
        return False
    if child == tree.left:
        return False
    if type(tree) not in associative:
        return False
    # Now check
    if not associative[type(tree)]:
        return True
    # Anything left to check
    if type(child) == type(tree):
        return False
    if not dual_associative[type(tree)]:
        return True
    return False

# Common class for all leaf nodes, i.e. nodes containing no expr children

class LeafNode:
    pass 

# Common class for all nodes with a left and right child (may be None)
class LRNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.paren = False # for temporary marking as in parentheses during parsing
        self.sort = None

    def paren_str(self, child):
        if not isatomic(child) and precedence[type(child)] > precedence[type(self)]:
            return '('+str(child)+')'
        elif needs_paren_right(self, child):
            return '('+str(child)+')'
        else:
            return str(child)

    def paren_repr(self, child):
        if not isatomic(child) and precedence[type(child)] > precedence[type(self)]:
            return '('+repr(child)+')'
        elif needs_paren_right(self, child):
            return '('+repr(child)+')'
        else:
            return repr(child)

# AST Nodes

class DeadNode(LeafNode):
    def __str__(self):
        return "----"

    def __repr__(self):
        return "----"

class SymbolNode(LeafNode):
    def __init__(self, name, constraint):
        self._name = name
        self.constraint = constraint
        self.sort = None

    def name(self):
        return self._name

    def __str__(self):
        if self.name() == "\\emptyset" and not isinstance(self.constraint, Universum) \
               and not (isinstance(self.constraint, SetOfNode) and \
                        isinstance(self.constraint.left, Universum)):
            return univar(self._name)+"("+str(self.constraint)+")"
        else:
            return univar(self._name)

    def __repr__(self):
        if self.name() == "\\emptyset" and not isinstance(self.constraint, Universum) \
               and not (isinstance(self.constraint, SetOfNode) and \
                        isinstance(self.constraint.left, Universum)):
            return self._name+"("+repr(self.constraint)+")"
        else:
            return self._name

class VarNode(LeafNode):
    def __init__(self, name, constraint=Universum(), is_metavar=False):
        self._name = name
        self.constraint = constraint
        self.sort = None
        self.is_metavar = is_metavar # whether this is a metavariable
        self.is_binder = False # whether this node is a binder variable
        self.skolemized = False # make sure we don't skolemize a variable twice

    def name(self):
        return self._name

    def __str__(self):
        return univar(self._name)+"\u0307" if self.is_metavar else univar(self._name)

    def __repr__(self):
        return "\\dot{"+self._name+"}" if self.is_metavar else self._name

class SetOfNode(LRNode):
    def __init__(self, var):
       self.left = var
       self.right = None

    def __str__(self):
       return str(self.left)

    def __repr__(self):
       return repr(self.left)

class NaturalNode(LeafNode):
    def __init__(self, string):
        self.value = int(string)
        self.constraint = NumberSort('\\mathbb{N}', OrderedSemiringClass())
        self.sort = SetSort(self.constraint)

    def __str__(self):
        return str(self.value)

    def __repr__(self):
        return str(self.value)

class ExpNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"^"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+"^"+self.paren_repr(self.right)

class CircNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"\u03bf"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\circ "+self.paren_repr(self.right)

class FnApplNode:
    def __init__(self, var, args):
        self.var = var # the function symbol (could be an expr like f \circ g)
        self.args = args
        self.sort = None
        self.is_skolem = False # Whether this is a skolem function
        self.is_metavar = False # Whether this is a metavariable
        self.is_binder = False # whether this function is a binder variable

    def name(self): # only used to compare against constant names
        return self.var.name() if isinstance(self.var, VarNode) or \
               isinstance(self.var, FnApplNode) else str(self.var)

    def __str__(self):
        if isinstance(self.var, VarNode):
            fn_name = self.var.name()
            name = univar(fn_name)+"\u0307" if self.is_metavar else univar(fn_name)
        elif isinstance(self.var, FnApplNode):
            name = str(self.var)
        else:
            name = "("+str(self.var)+")"
        sig = "("+', '.join(str(e) for e in self.args)+")" if self.args else ""
        return name+sig

    def __repr__(self):
        if isinstance(self.var, VarNode):
            fn_name = self.var.name()
        else:
            fn_name = "("+repr(self.var)+")"
        name = "\\dot{"+fn_name+"}" if self.is_metavar else fn_name
        sig = "("+', '.join(repr(e) for e in self.args)+")" if self.args else ""
        return name+sig

class LambdaNode(LRNode):
    def __str__(self):
        return "(\u03bb"+str(self.left)+" : "+str(self.right)+")"

    def __repr__(self):
        return "(\\lambda"+repr(self.left)+" : "+repr(self.right)+")"

class TupleNode:
    def __init__(self, args):
        self.name = '_'
        self.args = args
        self.sort = None

    def __str__(self):
        return "("+', '.join([str(s) for s in self.args])+")"

    def __repr__(self):
        return "("+', '.join([repr(s) for s in self.args])+")"

class TupleComponentNode(LRNode):
    def __init__(self, var, idx):
        self.left = var
        self.right = idx

    def __str__(self):
        return str(self.left)+"["+str(self.right)+"]"

    def __repr__(self):
        return repr(self.left)+"["+repr(self.right)+"]"

class PowerSetNode(LRNode):
    def __init__(self, arg):
        self.left = arg
        self.right = None

    def __str__(self):
        return "\u2118("+str(self.left)+")"

    def __repr__(self):
        return "\\mathcal{P}("+repr(self.left)+")"

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
        return self.paren_str(self.left)+" \u2264 "+self.paren_str(self.right)

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
        return self.paren_repr(self.left)+" \\iff "+self.paren_repr(self.right)

class AndNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2227 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\wedge "+self.paren_repr(self.right)

class OrNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2228 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\vee "+self.paren_repr(self.right)

class CartesianNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+"\u00d7"+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\times "+self.paren_repr(self.right)

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

class SubsetneqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2282 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\subsetneq "+self.paren_repr(self.right)

class SubseteqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2286 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\subseteq "+self.paren_repr(self.right)

class SupsetneqNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2283 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\supsetneq "+self.paren_repr(self.right)

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

class SetBuilderNode(LRNode):
    def __str__(self):
        return "{"+str(self.left)+" | "+str(self.right.right)+"}"

    def __repr__(self):
        return "{"+repr(self.left)+" | "+repr(self.right.right)+"}"

class AbsNode(LRNode):
    def __init__(self, expr):
        self.left = expr
        self.right = None

    def __str__(self):
        return "|"+str(self.left)+"|"

    def __repr__(self):
        return "|"+str(self.left)+"|"

class NotNode(LRNode):
    def __init__(self, expr):
        self.left = expr
        self.right = None

    def __str__(self):
        if not isatomic(self.left) and precedence[type(self.left)] > precedence[type(self)]:
            return "\u00ac"+'('+str(self.left)+')'
        else:
            return "\u00ac"+str(self.left)

    def __repr__(self):
        if not isatomic(self.left) and precedence[type(self.left)] > precedence[type(self)]:
            return "\\neg"+'('+repr(self.left)+')'
        else:
            return "\\neg"+repr(self.left)

class NegNode(LRNode):
    def __init__(self, expr):
        self.left = expr
        self.right = None

    def __str__(self):
        if not isatomic(self.left) and precedence[type(self.left)] > precedence[type(self)]:
            return "-("+str(self.left)+")"
        else:
            return "-"+str(self.left)

    def __repr__(self):
        if not isatomic(self.left) and precedence[type(self.left)] > precedence[type(self)]:
            return "-("+repr(self.left)+")"
        else:
            return "-"+repr(self.left)

class ExistsNode(LRNode):
    def __init__(self, var, expr):
        self.var = var
        self.left = expr
        self.right = None

    def __str__(self):
        if self.left:
            if isinstance(self.left, ForallNode) or isinstance(self.left, ExistsNode):
                  expr = ", "+str(self.left)
            else:
               expr = " "+str(self.left)
        else:
            expr = ""
        if isinstance(self.var.constraint, Universum):
                return "\u2203"+str(self.var)+expr
        elif isinstance(self.var.constraint, SetSort) or \
             isinstance(self.var.constraint, PredSort) or \
             isinstance(self.var.constraint, FunctionConstraint):
                return "\u2203"+str(self.var)+" : "+str(self.var.constraint)+expr
        else:
            return "\u2203"+str(self.var)+" \u2208 "+str(self.var.constraint)+expr

    def __repr__(self):
        if self.left:
            if isinstance(self.left, ForallNode) or isinstance(self.left, ExistsNode):
                  expr = ", "+repr(self.left)
            else:
               expr = " "+repr(self.left)
        else:
            expr = ""
        if isinstance(self.var.constraint, Universum):
                return "\\exists "+repr(self.var)+expr
        elif isinstance(self.var.constraint, SetSort) or \
             isinstance(self.var.constraint, PredSort) or \
             isinstance(self.var.constraint, FunctionConstraint):
                return "\\exists "+repr(self.var)+" : "+repr(self.var.constraint)+expr
        else:
            return "\\exists "+repr(self.var)+" \\in "+repr(self.var.constraint)+expr

class ForallNode(LRNode):
    def __init__(self, var, expr):
        self.var = var
        self.left = expr
        self.right = None

    def __str__(self):
        if self.left:
            if isinstance(self.left, ForallNode) or isinstance(self.left, ExistsNode):
                  expr = ", "+str(self.left)
            else:
               expr = " "+str(self.left)
        else:
            expr = ""
        if isinstance(self.var.constraint, Universum):
                return "\u2200"+str(self.var)+expr
        elif isinstance(self.var.constraint, SetSort) or \
             isinstance(self.var.constraint, PredSort) or \
             isinstance(self.var.constraint, FunctionConstraint):
                return "\u2200"+str(self.var)+" : "+str(self.var.constraint)+expr
        else:
            return "\u2200"+str(self.var)+" \u2208 "+str(self.var.constraint)+expr

    def __repr__(self):
        if self.left:
            if isinstance(self.left, ForallNode) or isinstance(self.left, ExistsNode):
                  expr = ", "+repr(self.left)
            else:
               expr = " "+repr(self.left)
        else:
            expr = ""
        if isinstance(self.var.constraint, Universum):
                return "\\forall "+repr(self.var)+expr
        elif isinstance(self.var.constraint, SetSort) or \
             isinstance(self.var.constraint, PredSort) or \
             isinstance(self.var.constraint, FunctionConstraint):
                return "\\forall "+repr(self.var)+" : "+repr(self.var.constraint)+expr
        else:
            return "\\forall "+repr(self.var)+" \\in "+repr(self.var.constraint)+expr

class ElemNode(LRNode):
    def __str__(self):
        return self.paren_str(self.left)+" \u2208 "+self.paren_str(self.right)

    def __repr__(self):
        return self.paren_repr(self.left)+" \\in "+self.paren_repr(self.right)

class BoolNode(LeafNode):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return "\u22A4" if self.value else "\u22A5"

    def __repr__(self):
        return "True" if self.value else "False"

precedence = {ExistsNode:9, ForallNode:9,
              ImpliesNode:8, IffNode:8,
              AndNode:7, OrNode:7,
              BoolNode:6,
              # Set nodes
              SubsetneqNode:6, SubseteqNode:6,
              SupsetneqNode:6, SupseteqNode:6, ElemNode:6,
              DiffNode:5,
              UnionNode:4, IntersectNode:4,
              CartesianNode:3,
              PowerSetNode:2, SetBuilderNode:2,
              # Function nodes
              CircNode:3,
              # Arithmetic nodes
              LeqNode:6, LtNode:6,
              GeqNode:6, GtNode:6,
              EqNode:6, NeqNode:6,
              AddNode:5, SubNode:5,
              NotNode:4,
              MulNode:3, DivNode:3,
              NegNode:2,
              ExpNode:1,
              SetOfNode:0, NaturalNode:0, VarNode:0, FnApplNode:0, AbsNode:0, TupleComponentNode:0}

# whether it is self associative
associative = {AddNode:True, SubNode:False, MulNode:True,
                 DivNode:False, ExpNode:False, CircNode:False,
                 UnionNode:True, IntersectNode:True,
                 DiffNode:False, ImpliesNode:False, IffNode:False}

# whether it associates with its dual
dual_associative = {AndNode:True, SubNode:False, MulNode:True,
                 DivNode:False, ExpNode:False, CircNode:False,
                 UnionNode:False, IntersectNode:False,
                 ImpliesNode:False, IffNode:False}

def mark_binder_vars(tree, var):
    if isinstance(tree, VarNode):
        if tree.name() == var.name():
            tree.is_binder = True
    elif isinstance(tree, LRNode):
        mark_binder_vars(tree.left, var)
        mark_binder_vars(tree.right, var)
    elif isinstance(tree, FnApplNode):
        if tree.name() == var.name():
            tree.is_binder = True
        for i in range(0, len(tree.args)):
            mark_binder_vars(tree.args[i], var)
    elif isinstance(tree, TupleNode):
        for i in range(0, len(tree.args)):
            mark_binder_vars(tree.args[i], var)

#####################################################################
# Nodes for automation

class AutoImplNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __str__(self):
        return "("+str(self.left)+", "+str(self.right)+")"

    def __repr__(self):
        return "("+repr(self.left)+", "+repr(self.right)+")"

class AutoEqNode:
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def __repr__(self):
        return "('=', "+repr(self.left)+", "+repr(self.right)+")"