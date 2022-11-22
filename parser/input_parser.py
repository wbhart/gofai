from parsimonious.grammar import Grammar

parse_hypothesis = Grammar(
    """
    hypothesis = type_hypothesis / substantive_hypothesis
    type_hypothesis = var space ":" space type_decl
    type_decl = dep_type / type_name
    dep_type = type_name "(" var ")"
    type_name = ~"[A-Z][A-Za-z]*"
    substantive_hypothesis = existential / universal / hypothesis_body
    hypothesis_body = space expression
    existential = "\\\\exists" space var space substantive_hypothesis
    universal = "\\\\forall" space var space substantive_hypothesis
    expression = (and_expression space "\\\\implies" space)* and_expression
    and_expression = (relation space ("\\\\wedge" / "\\\\vee") space)* relation
    relation = (add_expression space ("<" / ">" / "\\\\leq" / "\\\\geq" / "=" / "\\\\neq") space)* add_expression
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

