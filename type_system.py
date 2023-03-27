type_name = {"\\mathbb{N}" : "Naturals",
             "\\mathbb{Z}" : "Integers",
             "\\mathbb{R}" : "Reals",
             "\\mathbb{C}" : "Complex numbers"}

type_repr = {"Naturals" : "\\mathbb{N}",
              "Integers" : "\\mathbb{Z}",
              "Reals"    : "\\mathbb{R}",
              "Complex numbers" : "\\mathbb{C}"}

type_str = {"Naturals" : "\u2115",
              "Integers" : "\u2124",
              "Reals"    : "\u211d",
              "Complex numbers" : "\u2102"}

class NumberType:
    def __init__(self, name):
        self.name = type_name[name]

    def __repr__(self):
        return type_repr[self.name]

    def __str__(self):
        return type_str[self.name]
