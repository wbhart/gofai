from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor, Node
from parsimonious import exceptions
from pprint import pprint
from nodes import mark_binder_vars, AddNode, AndNode, NaturalNode, DiffNode, DivNode, \
     ElemNode, EqNode, ExistsNode, ExpNode, FnNode, ForallNode, GeqNode, \
     GtNode, IffNode, ImpliesNode, IntersectNode, LeqNode, LtNode, MulNode, \
     NotNode, NeqNode, OrNode, SubNode, SubsetneqNode, SubseteqNode, SupsetneqNode, \
     SupseteqNode, UnionNode, VarNode, BoolNode, AbsNode, ConstNode, NegNode, \
     SymbolNode, CartesianNode, TupleNode, PowerSetNode, SetBuilderNode, CircNode, \
     LRNode
from type import NumberType, FnType, TupleType, SetType, PredType

# TODO: add \sum, \integral, \partial, derivative, subscripts (incl. braces)

statement = Grammar(
    r"""
    statement = typed_constant / existential / exists / universal / forall / expression
    typed_constant = typed_var space ","? space statement?
    existential = exists space ","? space statement
    universal = forall space ","? space statement
    exists = "\\exists" space (typed_var / var)
    forall = "\\forall" space (typed_var / var)
    typed_var = var space ":" space type
    type = fn_type / basic_type
    basic_type = number_type / set_type / pred_type / set_expression
    pred_type = "Pred"
    fn_type = domain_type space "\\to" space basic_type
    domain_type = tuple_type / basic_type / set_expression
    tuple_type = "(" space (basic_type space "," space)* basic_type space ")"
    set_type = "Set" ("(" space (var / number_type) space ")")?
    number_type = "\\mathbb{N}" / "\\mathbb{Z}" / "\\mathbb{Q}" / "\\mathbb{R}" / "\\mathbb{C}" / "\\N" / "\\Z" / "\\Q" / "\\R" / "\\C"
    expression = (and_expression space ("\\implies" / "\\iff") space)* and_expression
    and_expression = (relation space ("\\wedge" / "\\vee") space)* relation
    relation = bool / elem_relation / subset_relation / equality / alg_relation / neg_expression / pred_paren / fn_application
    pred_paren = "(" statement ")"
    neg_expression = "\\neg" space (pred_paren / pred_fn / bool)
    equality = any_expression space "=" space any_expression
    any_expression = alg_expression / set_expression / var
    subset_relation = (set_expression space ("\\neq" / "\\subseteq" / "\\subsetneq" / "\\supseteq" / "\\supsetneq") space)+ set_expression
    elem_relation = (add_expression / set_expression) space "\\in" space set_expression
    set_expression = set_builder / circ_expression / set_diff / set_union / set_cartesian
    set_builder = "{" space elem_relation space "|" space expression space "}"
    set_diff = set_union space "\\setminus" space set_union
    set_union = (set_cartesian space ("\\cup" / "\\cap") space)* set_cartesian
    set_cartesian = (set space "\\times" space)* set
    set = universe / domain / codomain / complement / set_paren / var / number_type / empty_set / universum / powerset
    set_paren = "(" set_expression ")"
    universe = "universe(" space set_expression space ")"
    domain = "domain(" space var space ")"
    codomain = "codomain(" space var space ")"
    complement = "complement(" space set_expression space ")"
    powerset = "\\mathcal{P}(" space set_expression space ")"
    alg_relation = add_expression space ("<" / ">" / "\\leq" / "\\geq" / "\\neq") space add_expression
    alg_expression = left_alg_expression / right_alg_expression / minus_expression / mult_expression1 / alg_terminal
    left_alg_expression = terminal space ("+" / "-" / "*" / "/") space add_expression
    right_alg_expression = terminal space ("^" / "\\circ") space circ_expression
    add_expression = (mult_expression space ("+" / "-") space)* mult_expression
    mult_expression = mult_expression1 / mult_expression2 / minus_expression
    mult_expression1 = natural mult_expression2
    mult_expression2 = (exp_expression space ("*" / "/") space)* exp_expression
    minus_expression = "-" mult_expression
    circ_expression = var (space "\\circ" space var)+
    exp_expression = terminal (space "^" space terminal)*
    terminal = alg_terminal / var
    alg_terminal = tuple_expression / paren_expression / abs_expression / fn_application / composite_fn_app / natural
    bool = ("True" / "False")
    tuple_expression = "(" (add_expression space "," space)+ add_expression ")"
    paren_expression = "(" space alg_expression space ")"
    abs_expression = "|" add_expression "|"
    pred_fn = pred_name "(" (add_expression space "," space)* add_expression ")"
    fn_application = var "(" (any_expression space "," space)* any_expression ")"
    composite_fn_app = "(" circ_expression ")(" (any_expression space "," space)* any_expression ")"
    natural = ~"[1-9][0-9]*" / ~"0"
    pred_name = ~"is[A-Za-z0-9_]*" / ~"has[A-Za-z0-9_]*" / "\\alpha" / "\\beta" / "\\gamma" / "\\delta" / "\\epsilon" / "\\zeta" / "\\eta" / "\\kappa" / "\\lambda" / "\\mu" / "\\nu" / "\\psi" / "\\rho" / "\\sigma" / "\\chi" / "\\omega" / "\\tau" / "\\psi" / "\\phi"
    var = ~"[A-Za-z_][A-Za-z0-9_]*" / "\\alpha" / "\\beta" / "\\gamma" / "\\delta" / "\\epsilon" / "\\zeta" / "\\eta" / "\\kappa" / "\\lambda" / "\\mu" / "\\nu" / "\\psi" / "\\rho" / "\\sigma" / "\\chi" / "\\omega" / "\\tau" / "\\psi" / "\\phi"
    empty_set = "\\emptyset" ("(" space (var / number_type) space ")")?
    universum = "\\mathcal{U}"
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
    "\\supseteq" : SupseteqNode,
    "\\times" : CartesianNode,
    "\\circ" : CircNode
}

def is_alg_left_node(tree):
    return isinstance(tree, AddNode) or isinstance(tree, SubNode) or \
           isinstance(tree, MulNode) or isinstance(tree, DivNode)
           
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
        return ForallNode(visited_children[2][0], None)
    def visit_exists(self, node, visited_children):
        return ExistsNode(visited_children[2][0], None)
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
        types = [v[0] for v in visited_children[2]]
        types.append(visited_children[3])
        return TupleType(types)
    def visit_set_type(self, node, visited_children):
        params = visited_children[1]
        if isinstance(params, Node):
            return SetType(SymbolNode("\\mathcal{U}", None))
        else:
            return SetType(params[0][2][0])
    def visit_pred_type(self, node, visited_children):
        return PredType()
    def visit_universe(self, node, visited_children):
        return FnNode(VarNode("universe"), [visited_children[2]])
    def visit_domain(self, node, visited_children):
        return FnNode(VarNode("domain"), [visited_children[2]])
    def visit_codomain(self, node, visited_children):
        return FnNode(VarNode("codomain"), [visited_children[2]])
    def visit_complement(self, node, visited_children):
        return FnNode(VarNode("complement"), [visited_children[2]])
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
    def visit_set_cartesian(self, node, visited_children):
        sets = [v[0] for v in visited_children[0]]
        sets.append(visited_children[1])
        expr = sets[0]
        for v in sets[1:]:
            expr = CartesianNode(expr, v)
        return expr
    def visit_equality(self, node, visited_children):
        return EqNode(visited_children[0], visited_children[4])
    def visit_any_expression(self, node, visited_children):
        return visited_children[0]
    def visit_set_expression(self, node, visited_children):
        return visited_children[0]
    def visit_elem_relation(self, node, visited_children):
        return ElemNode(visited_children[0][0], visited_children[4])
    def visit_set_diff(self, node, visited_children):
        return DiffNode(visited_children[0], visited_children[4])
    def visit_set_union(self, node, visited_children):
        expr = visited_children[1]
        return left_rec(visited_children[0], expr)
    def visit_set(self, node, visited_children):
        return visited_children[0]
    def visit_set_paren(self, node, visited_children):
        return visited_children[1]
    def visit_powerset(self, node, visited_children):
        return PowerSetNode(visited_children[2])
    def visit_set_builder(self, node, visited_children):
        visited_children[2].left.is_binder = True
        mark_binder_vars(visited_children[6], visited_children[2].left)
        return SetBuilderNode(visited_children[2], visited_children[6])
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
    def visit_alg_expression(self, node, visited_children):
        return visited_children[0]
    def visit_left_alg_expression(self, node, visited_children):
        Node = node_dict[visited_children[2][0].text]
        t = visited_children[4]
        if not is_alg_left_node(t) or t.paren:
            return Node(visited_children[0], visited_children[4])
        while is_alg_left_node(t.left):
            t = t.left
        t.left = Node(visited_children[0], t.left)
        return visited_children[4]
    def visit_right_alg_expression(self, node, visited_children):
        Node = node_dict[visited_children[2][0].text]
        return Node(visited_children[0], visited_children[4])
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
    def visit_alg_terminal(self, node, visited_children):
        return visited_children[0]
    def visit_tuple_expression(self, node, visited_children):
        entries = [v[0] for v in visited_children[1]]
        entries.append(visited_children[2])
        return TupleNode(entries)
    def visit_paren_expression(self, node, visited_children):
        t = visited_children[2]
        if isinstance(t, LRNode):
            t.paren = True
        return t
    def visit_abs_expression(self, node, visited_children):
        return AbsNode(visited_children[1])
    def visit_fn_application(self, node, visited_children):
        args = []
        for v in visited_children[2]:
            args.append(v[0])
        args.append(visited_children[3])
        return FnNode(visited_children[0], args)
    def visit_composite_fn_app(self, node, visited_children):
        args = []
        for v in visited_children[3]:
            args.append(v[0])
        args.append(visited_children[4])
        return FnNode(visited_children[1], args)
    def visit_pred_fn(self, node, visited_children):
        args = []
        for v in visited_children[2]:
            args.append(v[0])
        args.append(visited_children[3])
        return FnNode(visited_children[0], args)
    def visit_pred_name(self, node, visited_children):
        return node.text
    def visit_exp_expression(self, node, visited_children):
        res = visited_children[0]
        for v in visited_children[1]:
            res = ExpNode(res, v[3])
        return res
    def visit_circ_expression(self, node, visited_children):
        res = visited_children[0]
        for v in visited_children[1]:
            res = CircNode(res, v[3])
        return res
    def visit_natural(self, node, visited_children):
        return NaturalNode(node.text)
    def visit_bool(self, node, visited_children):
        value = True if node.text == "True" else False
        return BoolNode(value)
    def visit_empty_set(self, node, visited_children):
        params = visited_children[1]
        if isinstance(params, Node):
            set_type = SetType(SymbolNode("\\mathcal{U}", None))
        else:
            set_type = SetType(params[0][2][0])
        return SymbolNode("\\emptyset", set_type)
    def visit_universum(self, node, visited_children):
        return SymbolNode("\\mathcal{U}", SetType(SymbolNode("\\mathcal{U}", None)))

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