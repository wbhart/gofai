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
        self._name = type_name[name]

    def __repr__(self):
        return type_repr[self._name]

    def __str__(self):
        return type_str[self._name]

    def name(self):
        return self._name
        
class NamedType:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
         return self.name

    def __str__(self):
         return self.name

class PredType:
    def __repr__(self):
       return "Pred"

    def __str__(self):
       return "Pred"

class SetType:
    def __init__(self, universe):
        self.universe = universe

    def __repr__(self):
        if self.universe.name() == '\\mathcal{U}':
            return "Set"
        else:
            return "Set("+repr(self.universe)+")"
            
    def __str__(self):
        if self.universe.name() == '\\mathcal{U}':
            return "Set"
        else:
            return "Set("+str(self.universe)+")"
            
class FnType:
    def __init__(self, domain, codomain):
         self.domain = domain
         self.codomain = codomain

    def __repr__(self):
         if self.domain == None:
             return repr(self.codomain)
         else:
             return repr(self.domain)+" \\to "+repr(self.codomain)

    def __str__(self):
         if self.domain == None:
             return str(self.codomain)
         else:
             return str(self.domain)+" \u2192 "+str(self.codomain)

class TupleType:
    def __init__(self, types):
         self.types = types

    def __repr__(self):
         n = len(self.types)
         if n == 0:
             return "()"
         else:
             return "("+', '.join([repr(self.types[i]) for i in range(0, n)])+")"
   
    def __str__(self):
         n = len(self.types)
         if n == 0:
             return "()"
         else:
             return "("+', '.join([str(self.types[i]) for i in range(0, n)])+")"
