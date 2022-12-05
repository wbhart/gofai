from parsimonious.grammar import Grammar

# TODO: add \sum, \integral, subscripts (incl. braces)

parse_hypothesis = Grammar(
    """
    hypothesis = type_hypothesis / substantive_hypothesis
    type_hypothesis = var space ":" space type_decl
    type_decl = dep_type / type_name
    dep_type = type_name "(" var ")"
    type_name = ~"[A-Z][A-Za-z]*"
    substantive_hypothesis = existential / universal / expression
    existential = "\\\\exists" space var space substantive_hypothesis
    universal = "\\\\forall" space var space substantive_hypothesis
    expression = (and_expression space "\\\\implies" space)* and_expression
    and_expression = (relation space ("\\\\wedge" / "\\\\vee") space)* relation
    relation = elem_relation / subset_relation / alg_relation
    subset_relation = (set_expression space ("\\\\subset" / "\\\\subseteq" / "\\\\supset" / "\\\\supseteq") space)+ set_expression
    elem_relation = add_expression space "\\\\in" space set_expression
    set_expression = set_diff / set_union
    set_diff = set_union space "\\\\setminus" space set_union
    set_union = (set space ("\\\\cup" / "\\\\cap") space)* set
    set = set_paren / var
    set_paren = "(" set_expression ")"
    alg_relation = (add_expression space ("<" / ">" / "\\\\leq" / "\\\\geq" / "=" / "\\\\neq") space)* add_expression
    add_expression = (mult_expression space ("+" / "-") space)* mult_expression
    mult_expression = mult_expression1 / mult_expression2
    mult_expression1 = const mult_expression2
    mult_expression2 = (exp_expression space ("*" / "/") space)* exp_expression
    exp_expression = terminal (space "^" space terminal)*
    terminal = paren_expression / fn_application / const / var / ("\\\\neg" space expression)
    paren_expression = "(" expression ")"
    fn_application = var "(" (add_expression space "," space)* add_expression ")"
    const = "-"? ~"[1-9][0-9]*"
    var = ~"[A-Za-z_][A-Za-z0-9_]*"
    space = ~"\s*"
    """)

