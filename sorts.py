from typeclass import SetClass, FunctionClass

sig_name = {"\\mathbb{N}" : "Natural",
             "\\mathbb{Z}" : "Integer",
             "\\mathbb{Q}" : "Rational",
             "\\mathbb{R}" : "Real",
             "\\mathbb{C}" : "Complex",
             "\\N" : "Natural",
             "\\Z" : "Integer",
             "\\Q" : "Rational",
             "\\R" : "Real",
             "\\C" : "Complex"}

sig_repr = {"Natural" : "\\mathbb{N}",
              "Integer" : "\\mathbb{Z}",
              "Rational" : "\\mathbb{Q}",
              "Real"    : "\\mathbb{R}",
              "Complex" : "\\mathbb{C}"}

sig_str = {"Natural" : "\u2115",
              "Integer" : "\u2124",
              "Rational" : "\u211a",
              "Real"    : "\u211d",
              "Complex" : "\u2102"}

def univar(name):
    if len(name) > 3 and name[-3] == '_' and name[-2:-1].isdigit():
        suffix = chr(8336+int(name[-1]))
        name = name[0:-3]
    elif len(name) > 2 and name[-2] == '_' and name[-1].isdigit():
        suffix = chr(8320+int(name[-1]))
        name = name[0:-2]
    else:
        suffix = ''

    unicode_dict = {"\\alpha" : "\u03b1",
                    "\\beta" : "\u03b2",
                    "\\gamma" : "\u03b3",
                    "\\delta" : "\u03b4",
                    "\\epsilon" : "\u03b5",
                    "\\zeta" : "\u03b6",
                    "\\eta" : "\u03b7",
                    "\\theta" : "\u03b8",
                    "\\kappa" : "\u03ba",
                    "\\lambda" : "\u03bb",
                    "\\mu" : "\u03bc",
                    "\\nu" : "\u03bd",
                    "\\xi" : "\u03be",
                    "\\rho" : "\u03c1",
                    "\\sigma" : "\u03c3",
                    "\\tau" : "\u03c4",
                    "\\phi" : "\u03c6",
                    "\\chi" : "\u03c7",
                    "\\psi" : "\u03c8",
                    "\\omega" : "\u03c9",
                    "\\emptyset" : "\u2205",
                    "\\mathcal{U}" : "\U0001d4b0"}

    if name in unicode_dict:
        return unicode_dict[name]+suffix
    else:
        return name+suffix

class Constraint:
    pass

class Sort(Constraint):
    pass

class FunctionConstraint(Constraint):
    def __init__(self, domain, codomain):
         self.domain = domain
         self.codomain = codomain
         if domain:
             # sort is that of single tuple in function which is
             # thought of as a set of tuples
             self.sort = TupleSort([domain.sort, codomain.sort])
         else:
             self.sort = TupleSort([None, codomain.sort]) # function is a constant

    def __repr__(self):
         if self.domain == None:
             return "() \\to "+repr(self.codomain)
         else:
             return repr(self.domain)+" \\to "+repr(self.codomain)

    def __str__(self):
         if self.domain == None:
             return "() \u2192 "+str(self.codomain)
         else:
             return str(self.domain)+" \u2192 "+str(self.codomain)

class DomainTuple(Constraint):
    def __init__(self, sets):
         self.sets = sets
         # sort is that of a tuple to be passed to a function
         self.sort = TupleSort([v.sort for v in sets])

    def __repr__(self):
         n = len(self.sets)
         if n == 0:
             return "()"
         else:
             return "("+', '.join([repr(self.sets[i]) for i in range(0, n)])+")"
   
    def __str__(self):
         n = len(self.sets)
         if n == 0:
             return "()"
         else:
             return "("+', '.join([str(self.sets[i]) for i in range(0, n)])+")"

class SetSort(Sort):
    def __init__(self, universe):
        self.sort = universe # element sort
        self.typeclass = SetClass()

    def __repr__(self):
        if isinstance(self.sort, Universum):
            return "Set"
        else:
            return "Set("+repr(self.sort)+")"
            
    def __str__(self):
        if isinstance(self.sort, Universum):
            return "Set"
        else:
            return "Set("+str(self.sort)+")"

class Universum(Sort):
    def __init__(self):
        self._name = "\\mathcal{U}"
        self.sort = self
        self.typeclass = SetClass()

    def __repr__(self):
        return self._name

    def __str__(self):
        return univar(self._name)

    def name(self):
        return self._name

class NumberSort(Sort):
    def __init__(self, name, typeclass):
        self._name = sig_name[name]
        self.sort = self
        self.typeclass = typeclass

    def __repr__(self):
        return sig_repr[self._name]

    def __str__(self):
        return sig_str[self._name]

    def name(self):
        return self._name

class TupleSort(Sort):
    def __init__(self, sets):
         self.sets = sets
         self.sort = self
         self.typeclass = SetClass()

    def __repr__(self):
         n = len(self.sets)
         if n == 0:
             return "()"
         else:
             return ' \\times '.join([repr(self.sets[i]) for i in range(0, n)])
   
    def __str__(self):
         n = len(self.sets)
         if n == 0:
             return "()"
         else:
             return '\u00d7'.join([str(self.sets[i]) for i in range(0, n)])

class PredSort(Sort):
    def __init__(self):
       self.sort = self

    def __repr__(self):
       return "Pred"

    def __str__(self):
       return "Pred"