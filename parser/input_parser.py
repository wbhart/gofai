from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor
from pprint import pprint
from parser.ast import AddNode, AndNode, ConstNode, DepNode, DiffNode, DivNode, \
     ElemNode, EqNode, ExistsNode, ExpNode, FnNode, ForallNode, GeqNode, GtNode, \
     IffNode, ImpliesNode, IntersectNode, LeqNode, LtNode, MulNode, NegNode, \
     NeqNode, OrNode, ParenNode, SubNode, SubsetNode, SubseteqNode, SupsetNode, \
     SupseteqNode, TypeNode, UnionNode, VarNode

# TODO: add \sum, \integral, \partial, derivative, subscripts (incl. braces)

parse_hypothesis = Grammar(
    r"""
    hypothesis = type_hypothesis / substantive_hypothesis
    type_hypothesis = var space ":" space type_decl
    type_decl = dep_type / type_name
    dep_type = type_name "(" var ")"
    type_name = ~"[A-Z][A-Za-z]*"
    substantive_hypothesis = existential / universal / neg_expression
    existential = "\\exists" space var space substantive_hypothesis
    universal = "\\forall" space var space substantive_hypothesis
    neg_expression = ("\\neg" space)? expression
    expression = (and_expression space ("\\implies" / "\\leftrightarrow") space)* and_expression
    and_expression = (relation space ("\\wedge" / "\\vee") space)* relation
    relation = elem_relation / subset_relation / alg_relation
    subset_relation = (set_expression space ("\\subseteq" / "\\subset" / "\\supseteq" / "\\supset") space)+ set_expression
    elem_relation = add_expression space "\\in" space set_expression
    set_expression = set_diff / set_union
    set_diff = set_union space "\\setminus" space set_union
    set_union = (set space ("\\cup" / "\\cap") space)* set
    set = set_paren / var
    set_paren = "(" set_expression ")"
    alg_relation = (add_expression space ("<" / ">" / "\\leq" / "\\geq" / "=" / "\\neq") space)? add_expression
    add_expression = (mult_expression space ("+" / "-") space)* mult_expression
    mult_expression = mult_expression1 / mult_expression2
    mult_expression1 = const mult_expression2
    mult_expression2 = (exp_expression space ("*" / "/") space)* exp_expression
    exp_expression = terminal (space "^" space terminal)*
    terminal = paren_expression / fn_application / const / var
    paren_expression = "(" neg_expression ")"
    fn_application = name "(" (add_expression space "," space)* add_expression ")"
    const = "-"? ~"[1-9][0-9]*"
    name = ~"[a-z][a-z0-9_]*"
    var = ~"[A-Za-z_][A-Za-z0-9_]*"
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
    "\\leftrightarrow" : IffNode,
    "\\cup" : UnionNode,
    "\\cap" : IntersectNode,
    "\\subset" : SubsetNode,
    "\\subseteq" : SubseteqNode,
    "\\supset" : SupsetNode,
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

class HypothesisVisitor(NodeVisitor):
    def generic_visit(self, node, visited_children):
        """ Generic visit method. """
        return visited_children or node
    def visit_hypothesis(self, node, visited_children):
        return visited_children[0]
    def visit_type_decl(self, node, visited_children):
        return visited_children[0]
    def visit_type_hypothesis(self, node, visited_children):
        return TypeNode(visited_children[0], visited_children[4])
    def visit_dep_type(self, node, visited_children):
        return DepNode(visited_children[0], visited_children[2])
    def visit_type_name(self, node, visited_children):
        return node.text
    def visit_substantive_hypothesis(self, node, visited_children):
        return visited_children[0]
    def visit_universal(self, node, visited_children):
        return ForallNode(visited_children[2], visited_children[4])
    def visit_existential(self, node, visited_children):
        return ExistsNode(visited_children[2], visited_children[4])
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
        return ParenNode(visited_children[1])
    def visit_neg_expression(self, node, visited_children):
        L = visited_children[0]
        expr = visited_children[1]
        if hasattr(L, '__getitem__'):
            return NegNode(expr)
        else:
            return expr
    def visit_expression(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_and_expression(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_alg_relation(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
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
    def visit_var(self, node, visited_children):
        return VarNode(node.text)
    def visit_terminal(self, node, visited_children):
        return visited_children[0]
    def visit_paren_expression(self, node, visited_children):
        return ParenNode(visited_children[1])
    def visit_fn_application(self, node, visited_children):
        args = []
        for v in visited_children[2]:
            args.append(v[0])
        args.append(visited_children[3])
        return FnNode(visited_children[0], args)
    def visit_name(self, node, visited_children):
        return node.text
    def visit_exp_expression(self, node, visited_children):
        res = visited_children[0]
        for v in visited_children[1]:
            res = ExpNode(res, v[3])
        return res
    def visit_const(self, node, visited_children):
        return ConstNode(node.text)
