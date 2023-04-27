type_name = {"\\mathbb{N}" : "Natural",
             "\\mathbb{Z}" : "Integer",
             "\\mathbb{Q}" : "Rational",
             "\\mathbb{R}" : "Real",
             "\\mathbb{C}" : "Complex",
             "\\N" : "Natural",
             "\\Z" : "Integer",
             "\\Q" : "Rational",
             "\\R" : "Real",
             "\\C" : "Complex"}

type_repr = {"Natural" : "\\mathbb{N}",
              "Integer" : "\\mathbb{Z}",
              "Rational" : "\\mathbb{Q}",
              "Real"    : "\\mathbb{R}",
              "Complex" : "\\mathbb{C}"}

type_str = {"Natural" : "\u2115",
              "Integer" : "\u2124",
              "Rational" : "\u211a",
              "Real"    : "\u211d",
              "Complex" : "\u2102"}

class NumberType:
    def __init__(self, name):
        self.name = type_name[name]

    def __repr__(self):
        return type_repr[self.name]

    def __str__(self):
        return type_str[self.name]

class NamedType:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
         return self.name

    def __str__(self):
         return self.name

class FnType:
    def __init__(self, domain, codomain):
         self.domain = domain
         self.codomain = codomain

    def __repr__(self):
         return repr(self.domain)+" \\to "+repr(self.codomain)

    def __str__(self):
         return str(self.domain)+" \u2192 "+str(self.codomain)