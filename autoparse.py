from parsimonious.grammar import Grammar
from parsimonious.nodes import NodeVisitor, Node
from parsimonious import exceptions
from nodes import AutoImplNode, AutoIffNode, AutoEqNode

conststring = Grammar(
    r"""
    conststring = "[" list ", " list ", " thmlist "]"
    thmlist = (thm ", ")* thm
    thm = strlist / eqlistpair / ifflistpair / listpair
    list = emptylist / strlist
    listpair = "(" list ", " list ")"
    eqlistpair = "('=', " list ", " list ")"
    ifflistpair = "('\\\\iff', " list ", " list ")"
    emptylist = "[]"
    strlist = "[" (text "," space)* text "]"
    space = ~"\s*"
    text = ~"'[^']*'"
    """)

class ConststringVisitor(NodeVisitor):
    def generic_visit(self, node, visited_children):
        """ Generic visit method. """
        return visited_children or node
    def visit_conststring(self, node, visited_children):
        return visited_children[1], visited_children[3], visited_children[5]
    def visit_thmlist(self, node, visited_children):
        list1 = visited_children[0]
        thm1 = visited_children[1]
        return [thm1] if isinstance(list1, Node) else [v[0] for v in list1] + [thm1]
    def visit_thm(self, node, visited_children):
        return visited_children[0]
    def visit_list(self, node, visited_children):
        return visited_children[0]
    def visit_listpair(self, node, visited_children):
        return AutoImplNode(visited_children[1], visited_children[3])
    def visit_ifflistpair(self, node, visited_children):
        return AutoIffNode(visited_children[1], visited_children[3])
    def visit_eqlistpair(self, node, visited_children):
        return AutoEqNode(visited_children[1], visited_children[3])
    def visit_emptylist(self, node, visited_children):
        return []
    def visit_strlist(self, node, visited_children):
        list1 = visited_children[1]
        str1 = visited_children[2]
        return [str1] if isinstance(list1, Node) else [v[0] for v in list1] + [str1]
    def visit_text(self, node, visited_children):
        return eval(node.text)

def parse_consts(screen, string):
    try:
        ast = conststring.parse(string) # parse input
        visitor = ConststringVisitor()
        return True, visitor.visit(ast)
    except exceptions.IncompleteParseError as inst:
        index = inst.args[1]
        return False, "Extra characters on line, starting at column "+str(index + 1)
    except exceptions.ParseError as inst:
        index = inst.pos
        return False, "Error in statement starting at column "+str(index + 1)