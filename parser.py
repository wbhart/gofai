from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor, Node
from parsimonious import exceptions
from pprint import pprint
from nodes import AddNode, AndNode, NaturalNode, DiffNode, DivNode, \
     ElemNode, EqNode, ExistsNode, ExpNode, FnNode, ForallNode, GeqNode, \
     GtNode, IffNode, ImpliesNode, IntersectNode, LeqNode, LtNode, MulNode, \
     NotNode, NeqNode, OrNode, SubNode, SubsetneqNode, SubseteqNode, SupsetneqNode, \
     SupseteqNode, UnionNode, VarNode, BoolNode, AbsNode, ConstNode, NegNode, \
     SymbolNode
from type import NumberType, NamedType, FnType, TupleType

# TODO: add \sum, \integral, \partial, derivative, subscripts (incl. braces)

statement = Grammar(
    r"""
    statement = typed_constant / existential / exists / universal / forall / expression
    typed_constant = typed_var space ","? space statement?
    existential = exists space ","? space statement
    universal = forall space ","? space statement
    exists = "\\exists" space typed_var
    forall = "\\forall" space typed_var
    typed_var = var space ":" space type
    type = fn_type / basic_type
    basic_type = number_type / named_type
    fn_type = domain_type space "\\to" space basic_type
    domain_type = tuple_type / basic_type
    tuple_type = "(" space (basic_type space "," space)* basic_type space ")"
    named_type = "Set"
    number_type = "\\mathbb{N}" / "\\mathbb{Z}" / "\\mathbb{Q}" / "\\mathbb{R}" / "\\mathbb{C}" / "\\N" / "\\Z" / "\\Q" / "\\R" / "\\C"
    expression = (and_expression space ("\\implies" / "\\iff") space)* and_expression
    and_expression = (relation space ("\\wedge" / "\\vee") space)* relation
    relation = bool / elem_relation / subset_relation / alg_relation / neg_expression / pred_paren
    pred_paren = "(" statement ")"
    neg_expression = "\\neg" space (paren_expression / pred_fn / bool)
    subset_relation = (set_expression space ("=" / "\\neq" / "\\subseteq" / "\\subsetneq" / "\\supseteq" / "\\supsetneq") space)+ set_expression
    elem_relation = add_expression space "\\in" space set_expression
    set_expression = set_diff / set_union
    set_diff = set_union space "\\setminus" space set_union
    set_union = (set space ("\\cup" / "\\cap") space)* set
    set = set_paren / var / number_type / empty_set
    set_paren = "(" set_expression ")"
    alg_relation = add_expression space ("<" / ">" / "\\leq" / "\\geq" / "=" / "\\neq") space add_expression
    add_expression = (mult_expression space ("+" / "-") space)* mult_expression
    mult_expression = mult_expression1 / mult_expression2 / minus_expression
    mult_expression1 = natural mult_expression2
    mult_expression2 = (exp_expression space ("*" / "/") space)* exp_expression
    minus_expression = "-" mult_expression
    exp_expression = terminal (space "^" space terminal)*
    terminal = paren_expression / abs_expression / fn_application / natural / var
    bool = ("True" / "False")
    paren_expression = "(" add_expression ")"
    abs_expression = "|" add_expression "|"
    pred_fn = pred_name "(" (add_expression space "," space)* add_expression ")"
    fn_application = name "(" (add_expression space "," space)* add_expression ")"
    natural = ~"[1-9][0-9]*" / ~"0"
    pred_name = ~"is[A-Za-z0-9_]*" / ~"has[A-Za-z0-9_]*" / "\\alpha" / "\\beta" / "\\gamma" / "\\delta" / "\\epsilon" / "\\zeta" / "\\eta" / "\\kappa" / "\\lambda" / "\\mu" / "\\nu" / "\\psi" / "\\rho" / "\\sigma" / "\\chi" / "\\omega" / "\\tau" / "\\psi" / "\\phi"
    name = ~"[A-Za-z_][A-Za-z0-9_]*" / "\\alpha" / "\\beta" / "\\gamma" / "\\delta" / "\\epsilon" / "\\zeta" / "\\eta" / "\\kappa" / "\\lambda" / "\\mu" / "\\nu" / "\\psi" / "\\rho" / "\\sigma" / "\\chi" / "\\omega" / "\\tau" / "\\psi" / "\\phi"
    var = ~"[A-Za-z_][A-Za-z0-9_]*" / "\\alpha" / "\\beta" / "\\gamma" / "\\delta" / "\\epsilon" / "\\zeta" / "\\eta" / "\\kappa" / "\\lambda" / "\\mu" / "\\nu" / "\\psi" / "\\rho" / "\\sigma" / "\\chi" / "\\omega" / "\\tau" / "\\psi" / "\\phi"
    empty_set = "\\emptyset"
    space = ~"\s*"
    """)

node_dict = {
    "+" : AddNode,
    "-" : SubNode,
    "*" : MulNode,
    "/" : DivNode,
    "<" : LtNode,
    ">" : GtNode,
    "\\leq" : LeqNode,
    "\\geq" : GeqNode,
    "=" : EqNode,
    "\\neq" : NeqNode,
    "\\wedge" : AndNode,
    "\\vee" : OrNode,
    "\\implies" : ImpliesNode,
    "\\iff" : IffNode,
    "\\cup" : UnionNode,
    "\\cap" : IntersectNode,
    "\\subsetneq" : SubsetneqNode,
    "\\subseteq" : SubseteqNode,
    "\\supsetneq" : SupsetneqNode,
    "\\supseteq" : SupseteqNode
}

def left_rec(L, v):
    """Turn a list L and final value v into a tree. Each element of the list
    will contain 4 items [v, _, op, _]. If L is empty only v is returned.
    """
    if hasattr(L, '__getitem__') and len(L) > 0:
        x = L.pop()
        Node = node_dict[x[2][0].text]
        return Node(left_rec(L, x[0]), v)
    else:
        return v

class StatementVisitor(NodeVisitor):
    def generic_visit(self, node, visited_children):
        """ Generic visit method. """
        return visited_children or node
    def visit_statement(self, node, visited_children):
        return visited_children[0]
    def visit_typed_constant(self, node, visited_children):
        if isinstance(visited_children[4], Node):
            return ConstNode(visited_children[0], None)
        else:
            return ConstNode(visited_children[0], visited_children[4][0])
    def visit_universal(self, node, visited_children):
        expr = visited_children[4]
        quantor = visited_children[0]
        quantor.left = expr
        return quantor
    def visit_existential(self, node, visited_children):
        expr = visited_children[4]
        quantor = visited_children[0]
        quantor.left = expr
        return quantor
    def visit_forall(self, node, visited_children):
        return ForallNode(visited_children[2], None)
    def visit_exists(self, node, visited_children):
        return ExistsNode(visited_children[2], None)
    def visit_typed_var(self, node, visited_children):
        visited_children[0].type = visited_children[4]
        return visited_children[0]
    def visit_type(self, node, visited_children):
        return visited_children[0]
    def visit_basic_type(self, node, visited_children):
        return visited_children[0]
    def visit_domain_type(self, node, visited_children):
        return visited_children[0]
    def visit_tuple_type(self, node, visited_children):
        types = [v[0] for v in visited_children[2]].push(visited_children[3])
        return TupleType(types)
    def visit_named_type(self, node, visited_children):
        return NamedType(node.text)
    def visit_number_type(self, node, visited_children):
        return NumberType(node.text)
    def visit_fn_type(self, node, visited_children):
        return FnType(visited_children[0], visited_children[4])
    def visit_predicate(self, node, visited_children):
        return visited_children[0]
    def visit_pred_paren(self, node, visited_children):
        return visited_children[1]
    def visit_relation(self, node, visited_children):
        return visited_children[0]
    def visit_subset_relation(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_set_expression(self, node, visited_children):
        return visited_children[0]
    def visit_elem_relation(self, node, visited_children):
        return ElemNode(visited_children[0], visited_children[4])
    def visit_set_diff(self, node, visited_children):
        return DiffNode(visited_children[0], visited_children[4])
    def visit_set_union(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_set(self, node, visited_children):
        return visited_children[0]
    def visit_set_paren(self, node, visited_children):
        return visited_children[1]
    def visit_neg_expression(self, node, visited_children):
        return NotNode(visited_children[2][0])
    def visit_expression(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_and_expression(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_alg_relation(self, node, visited_children):
        expr = visited_children[4]
        Node = node_dict[visited_children[2][0].text]
        return Node(visited_children[0], expr)
    def visit_add_expression(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_mult_expression(self, node, visited_children):
        return visited_children[0]
    def visit_mult_expression1(self, node, visited_children):
        return MulNode(visited_children[0], visited_children[1])
    def visit_mult_expression2(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_minus_expression(self, node, visited_children):
        return NegNode(visited_children[1])
    def visit_var(self, node, visited_children):
        return VarNode(node.text)
    def visit_terminal(self, node, visited_children):
        return visited_children[0]
    def visit_paren_expression(self, node, visited_children):
        return visited_children[1]
    def visit_abs_expression(self, node, visited_children):
        return AbsNode(visited_children[1])
    def visit_fn_application(self, node, visited_children):
        args = []
        for v in visited_children[2]:
            args.append(v[0])
        args.append(visited_children[3])
        return FnNode(visited_children[0], args)
    def visit_pred_fn(self, node, visited_children):
        args = []
        for v in visited_children[2]:
            args.append(v[0])
        args.append(visited_children[3])
        return FnNode(visited_children[0], args)
    def visit_name(self, node, visited_children):
        return node.text
    def visit_pred_name(self, node, visited_children):
        return node.text
    def visit_exp_expression(self, node, visited_children):
        res = visited_children[0]
        for v in visited_children[1]:
            res = ExpNode(res, v[3])
        return res
    def visit_natural(self, node, visited_children):
        return NaturalNode(node.text)
    def visit_bool(self, node, visited_children):
        value = True if node.text == "True" else False
        return BoolNode(value)
    def visit_empty_set(self, node, visited_children):
        return SymbolNode("\\emptyset", NamedType("Set"))

def to_ast(screen, string):
    try:
        ast = statement.parse(string) # parse input
        visitor = StatementVisitor()
        return visitor.visit(ast)
    except exceptions.IncompleteParseError as inst:
        index = inst.args[1]
        screen.dialog("Extra characters on line, starting at column "+str(index + 1)+". Press ENTER to continue")
    except exceptions.ParseError as inst:
        index = inst.pos
        screen.dialog("Error in statement starting at column "+str(index + 1)+". Press ENTER to continue")
    return index