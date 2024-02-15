from utility import unquantify, relabel, append_tree, replace_tree, \
     add_descendant, target_compatible, complement_tree, process_constraints, \
     get_constants, merge_lists, skolemize_quantifiers, skolemize_statement, \
     add_sibling, vars_used, domain, codomain, universe, metavars_used, \
     tags_to_list, canonicalise_tags, record_move, duplicate_move, mark_shared
from unification import check_macros, unify, substitute, same_tree
from copy import deepcopy
from nodes import AndNode, OrNode, ImpliesNode, LRNode, LeafNode, ForallNode, \
     ExistsNode, TupleNode, FnApplNode, NotNode, IffNode, SetOfNode, EqNode, \
     SymbolNode, SubseteqNode, VarNode
from parser import to_ast
from sorts import FunctionConstraint, DomainTuple, PredSort

def fill_macros(screen, tl):
    """
    When the tableau is initially loaded, before any processing whatsoever,
    there may be macros in the tableau (universe, domain, codomain, etc.)
    which need to be computed. This function also needs to be called every
    move as it is possible that some inference filled in a metavariable,
    at which point a macro with that variable as parameter may now be
    computed. Generally, this function must be called before any processing
    of constraints or sorts. The only macros that can't be filled in are
    those whose parameter is a metavariable about which the required
    information is not known. This happens for example when theorems are
    loaded from the library, before they are instantiated.
    """
    def fill(tree, data):
        if tree == None:
            return None
        if isinstance(tree, FnApplNode):
            if tree.name() == 'universe':
                return SetOfNode(universe(tree.args[0], data))
            if tree.name() == 'domain':
                return domain(tree.args[0], data)
            if tree.name() == 'codomain':
                return codomain(tree.args[0], data)
            for i in range(0, len(tree.args)):
                tree.args[i] = fill(tree.args[i], data)
            return tree
        elif isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            tree.var.constraint = fill(tree.var.constraint, data)
            new_data = deepcopy(tree)
            new_data.left = data
            tree.left = fill(tree.left, new_data)
            return tree
        elif isinstance(tree, TupleNode):
            for i in range(0, len(tree.args)):
                tree.args[i] = fill(tree.args[i], data)
            return tree
        elif isinstance(tree, LRNode):
            tree.left = fill(tree.left, data)
            tree.right = fill(tree.right, data)
            return tree
        elif isinstance(tree, SymbolNode):
            tree.constraint = fill(tree.constraint, data)
            return tree
        elif isinstance(tree, LeafNode):
            return tree
        else:
            return tree

    data = tl.tlist0.data[0] if tl.tlist0.data else []
    #if len(tl.tlist0.data) > 0:
    #    tl.tlist0.data[0] = fill(tl.tlist0.data[0], data)  
    for i in range(0, len(tl.tlist1.data)):
        tl.tlist1.data[i] = fill(tl.tlist1.data[i], data)
    for i in range(0, len(tl.tlist2.data)):
        tl.tlist2.data[i] = fill(tl.tlist2.data[i], data)

def modus_ponens(screen, tl, ttree, dep, line1, line2_list, forward):
    """
    Given an implication on line1 of the hypothesis pane (numbered from 0)
    and a list of predicates on the lines in line2_list, which will be in
    the hypotheses if forward=True, otherwise in the targets, apply the
    modus ponens move where the precedent of the implication is unified with a
    conjunction of the specified predicates. The consequence of the implication
    is then appended to the tableau, with appropriate target dependency
    specified by dep (for an example of how to compute this, see the
    modus_ponens function in the moves modules).

    If the predicate(s) could not be unified with the precedent of the
    implication then the function returns False, otherwise True.

    Of course unification is done with the right side of the implication
    instead of the left if forward=False.

    As a special case, line2_list can contain just a single line2 which may
    be an implication. In this case P => Q is interpreted as ¬P \wedge Q,
    i.e. the predicates are taken to be ¬P and Q instead of predicates
    explicitly specified in line2_list.

    Although screen is passed to this function, it is never used and None
    can be passed if required. The parameter exists only to make debugging
    easier in terminal mode.

    The function is passed a target tree (ttree) which keeps track of which
    targets are required to prove which other targets. This is updated if a
    new target is appended.
    """
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2

    dirty1 = [] # list of hyps that need updating in the interface
    dirty2 = [] # list of tars that need updating in the interface

    tree1 = tlist1.data[line1]
    tree1, univs = unquantify(screen, tree1, False) # remove quantifiers by taking temporary metavars
    
    if forward:
        qP1, u = unquantify(screen, tree1.left, True)
    else:
        tree1, copied = relabel(screen, tl, univs, tree1, True)
        qP1, u = unquantify(screen, tree1.right, False)
    
    line2 = line2_list[0]
    tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
    
    for i in range(1, len(line2_list)):
        line2 = line2_list[i]
        new_tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
        tree2 = AndNode(tree2, new_tree2)
    
    qP2 = tree2
    conseq = tree1.right if forward else tree1.left
    
    if isinstance(qP2, ImpliesNode):
        # treat P => Q as ¬P \wedge Q
        # temporary relabelling
        unifies, assign, macros = unify(screen, tl, qP1, complement_tree(relabel(screen, tl, [], deepcopy(qP2.left), temp=True)[0]), allow_shared=False)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
        if unifies:
            # temporary relabelling
            unifies, assign, macros = unify(screen, tl, qP1, relabel(screen, tl, [], deepcopy(qP2.right), temp=True)[0], assign, allow_shared=False)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    else:
        unifies, assign, macros = unify(screen, tl, qP1, qP2, allow_shared=False)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    if not unifies:
        return False, dirty1, dirty2 # fail: predicate does not match implication
    stmt = substitute(deepcopy(conseq), assign)
    if forward:
        stmt, _ = relabel(screen, tl, univs, stmt, True, assign=assign)
        append_tree(tlist1.data, stmt, dirty1)
        n = len(tlist1.data) - 1
        tlist1.dep[n] = dep
        record_move(screen, tl, n, ('p', line1, line2_list))
    else:
        if copied:
            substitute(copied[0], assign)
        if line2 in tl.tars: # we already reasoned from this target
            stmt = complement_tree(stmt)
            append_tree(tlist1.data, stmt, dirty1) # add negation to hypotheses
            n = len(tlist1.data) - 1
            tlist1.dep[n] = [line2]
            record_move(screen, tl, n, ('p', line1, []))
        else:
            append_tree(tlist2.data, stmt, dirty2)
            add_descendant(ttree, line2, len(tlist2.data) - 1, line1)
            tl.tars[line2] = True
    return True, dirty1, dirty2

def modus_tollens(screen, tl, ttree, dep, line1, line2_list, forward):
    """
    Given an implication on line1 of the hypothesis pane (numbered from 0)
    and a list of predicates on the lines in line2_list, which will be in
    the hypotheses if forward=True, otherwise in the targets, apply the
    modus tollens move where the *negation* of the consequent of the
    implication is unified with a conjunction of specified predicates.
    The precedent of the implication is then appended to the tableau, with
    appropriate target dependency specified by dep (for an example of how to
    compute this, see the modus_tollens function in the moves modules).

    If the predicate(s) could not be unified with the negation of the
    consequent of the implication then the function returns False, otherwise
    True.

    Of course unification is done with the left side of the implication
    instead of the right if forward=False.

    As a special case, line2_list can contain just a single line2 which may
    be an implication. In this case P => Q is interpreted as ¬P \wedge Q,
    i.e. the predicates are taken to be ¬P and Q instead of predicates
    explicitly specified in line2_list.

    Although screen is passed to this function, it is never used and None
    can be passed if required. The parameter exists only to make debugging
    easier in terminal mode.

    The function is passed a target tree (ttree) which keeps track of which
    targets are required to prove which other targets. This is updated if a
    new target is appended.
    """
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2

    dirty1 = [] # list of hyps that need updating in the interface
    dirty2 = [] # list of tars that need updating in the interface

    tree1 = tlist1.data[line1]
    tree1, univs = unquantify(screen, tree1, False) # remove quantifiers by taking temporary metavars
    
    if forward:
        qP1, u = unquantify(screen, tree1.right, False)
    else:
        tree1, copied = relabel(screen, tl, univs, tree1, True)
        qP1, u = unquantify(screen, tree1.left, True)
    
    qP1 = complement_tree(qP1) # modus tollens unifies with complement

    line2 = line2_list[0]
    tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
    
    for i in range(1, len(line2_list)):
        line2 = line2_list[i]
        new_tree2 = tlist1.data[line2] if forward else tlist2.data[line2]
        tree2 = AndNode(tree2, new_tree2)
    
    qP2 = tree2
    conseq = tree1.left if forward else tree1.right
    if isinstance(qP2, ImpliesNode):
        # treat P => Q as ¬P \wedge Q
        # temporary relabelling
        unifies, assign, macros = unify(screen, tl, qP1, complement_tree(relabel(screen, tl, [], deepcopy(qP2.left), temp=True)[0]), allow_shared=False)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
        if unifies:
            # temporary relabelling
            unifies, assign, macros = unify(screen, tl, qP1, relabel(screen, tl, [], deepcopy(qP2.right), temp=True)[0], assign, allow_shared=False)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    else:
        unifies, assign, macros = unify(screen, tl, qP1, qP2, allow_shared=False)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    if not unifies:
        return False, dirty1, dirty2 # fail: predicate does not match implication
    stmt = complement_tree(substitute(deepcopy(conseq), assign))
    if forward:
        stmt, _ = relabel(screen, tl, univs, stmt, True, assign=assign)
        append_tree(tlist1.data, stmt, dirty1)
        n = len(tlist1.data) - 1
        tlist1.dep[n] = dep
        record_move(screen, tl, n, ('t', line1, line2_list))
    else:
        if copied:
            substitute(copied[0], assign)
        if line2 in tl.tars: # we already reasoned from this target
            stmt = complement_tree(stmt)
            append_tree(tlist1.data, stmt, dirty1) # add negation to hypotheses
            n = len(tlist1.data) - 1
            tlist1.dep[n] = [line2]
            record_move(screen, tl, n, ('t', line1, []))
        else:
            append_tree(tlist2.data, stmt, dirty2)
            add_descendant(ttree, line2, len(tlist2.data) - 1, line1)
            tl.tars[line2] = True
    return True, dirty1, dirty2

def equality_substitution(screen, tl, line1, line2, is_hyp, string, n):
    """
    Given that line1 of the hypothesis pane is an equality to be applied, apply
    that equality to the n-th occurrence of the statement at line2 with exact
    string representation equal to the given string. Numbering of occurrences
    of string in this statement begins at 0.

    If is_hyp = True, the statement to which the substitution is to be applied
    is a hypothesis, otherwise it is a target.

    The equality is first tried one way around, and if it fails, it is tried
    the other way around. The expression that is to be modified need not match
    one side of the equality exactly, it merely needs to unify with it. Any
    assignments that result from unification are also applied.

    If for some reason the unification fails, the function returns False and
    no changes are made. Otherwise the tableau is updated with the changes.
    """
    subst = tl.tlist1.data[line1]
    subst, univs = unquantify(screen, subst, True)
    tree = tl.tlist1.data[line2] if is_hyp else tl.tlist2.data[line2]
    
    def find(tree, string, n, subst, occurrence=-1):
        occur = occurrence
        found = False
        if tree == None:
            return False, None
        if str(tree) == string: # we found an occurrence
            occur += 1
            if occur == n: # we found the right occurrence
                unifies, assign, macros = unify(screen, tl, subst.left, tree, allow_shared=False)
                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                if not unifies:
                    unifies, assign, macros = unify(screen, tl, subst.right, tree, allow_shared=False)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if not unifies:
                        return False, tree # does not unify, bogus selection
                    else:
                        return True, substitute(deepcopy(subst.left), assign)
                else:
                    return True, substitute(deepcopy(subst.right), assign)
        if isinstance(tree, LRNode):
            found, tree.left = find(tree.left, string, n, subst, occur)
            if not found:
                found, tree.right = find(tree.right, string, n, subst, occur)
            return found, tree
        elif isinstance(tree, LeafNode):
            return found, tree
        elif isinstance(tree, TupleNode) or isinstance (tree, FnApplNode):
            for i in range(0, len(tree.args)):
                 found, tree.args[i] = find(tree.args[i], string, n, subst, occur)
                 if found:
                     break
            if not found and isinstance(tree, FnApplNode):
                found, tree.var = find(tree.var, string, n, subst, occur)
            return found, tree
        raise Exception("Node not dealt with : "+str(type(tree)))

    found, tree = find(tree, string, n, subst)
    if found:
        tree = substitute(tree, assign) # we may have assigned metavars used elsewhere in the expression
        if is_hyp:
            append_tree(tl.tlist1.data, tree, dirty1)
            n = len(tl.tlist1.data) - 1
            tl.tlist1.dep[n] = dep
            record_move(screen, tl, n, ('e', line1, [line2]))
        else:
            if line2 in tl.tars: # we already reasoned from this target
                tree = complement_tree(tree)
                append_tree(tl.tlist1.data, tree, dirty1) # add negation to hypotheses
                n = len(tl.tlist1.data) - 1
                tl.tlist1.dep[n] = [line2]
                record_move(screen, tl, n, ('e', line1, []))
            else:
                append_tree(tl.tlist2.data, tree, dirty2)
                add_descendant(ttree, line2, len(tl.tlist2.data) - 1, line1)
                tl.tars[line2] = True
    return found

def limited_equality_substitution(screen, tl, ttree, dep, line1, line2, is_hyp, check_only=False):
    """
    Given that line1 of the hypothesis pane is an equality to be applied, apply
    that equality to the first full term of the statement at line2 to which it
    applies.

    If is_hyp = True, the statement to which the substitution is to be applied
    is a hypothesis, otherwise it is a target.

    The expression that is to be modified need not match one side of the equality
    exactly, it merely needs to unify with it. Any assignments that result from
    unification are also applied.

    If for some reason the unification fails, the function returns False and
    no changes are made. Otherwise if check_only is False, the tableau is
    augmented with the modified version. If check_only is True the function
    simply returns whether or not a place was found where the substitution
    could be applied.
    """
    subst = tl.tlist1.data[line1]
    subst, univs = unquantify(screen, subst, True)
    tree = tl.tlist1.data[line2] if is_hyp else tl.tlist2.data[line2]
    if metavars_used(tree): # ensure we are transforming something concrete
        return False, None, None 
    if not check_only:
        tree = deepcopy(tree)
        dirty1 = []
        dirty2 = []

    def find(tree, subst):
        found = False
        if tree == None:
            return False, None, None
        if not isinstance(tree.sort, PredSort): # we found a term
            left = subst.left
            right = subst.right
            unifies, assign, macros = unify(screen, tl, left, tree, allow_shared=False)
            if not check_only:
                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
            if not unifies:
                return False, tree, None # does not unify, bogus selection
            else:
                if check_only:
                    return True, tree, None
                else:
                    return True, substitute(deepcopy(right), assign), assign
        if isinstance(tree, LRNode):
            found, tree.left, assign = find(tree.left, subst)
            if not found:
                found, tree.right, assign = find(tree.right, subst)
            return found, tree, assign
        elif isinstance(tree, LeafNode):
            return found, tree, None
        elif isinstance(tree, TupleNode) or isinstance (tree, FnApplNode):
            for i in range(0, len(tree.args)):
                 found, tree.args[i], assign = find(tree.args[i], subst)
                 if found:
                     break
            if not found and isinstance(tree, FnApplNode):
                found, tree.var, assign = find(tree.var, subst)
            return found, tree, assign
        raise Exception("Node not dealt with : "+str(type(tree)))

    found, tree, assign = find(tree, subst)
    if not check_only and found:
        tree = substitute(tree, assign) # we may have assigned metavars used elsewhere in the expression
        if is_hyp:
            append_tree(tl.tlist1.data, tree, dirty1)
            n = len(tl.tlist1.data) - 1
            tl.tlist1.dep[n] = dep
            record_move(screen, tl, n, ('e', line1, [line2]))
        else:
            if line2 in tl.tars: # we already reasoned from this target
                tree = complement_tree(tree)
                append_tree(tl.tlist1.data, tree, dirty1) # add negation to hypotheses
                n = len(tl.tlist1.data) - 1
                tl.tlist1.dep[n] = [line2]
                record_move(screen, tl, n, ('e', line1, []))
            else:
                append_tree(tl.tlist2.data, tree, dirty2)
                add_descendant(ttree, line2, len(tl.tlist2.data) - 1, line1)
                tl.tars[line2] = True
    if check_only:
        return found, None, None
    else:
        return found, dirty1, dirty2

def clear_tableau(screen, tl):
    """
    Clear the tableau and reset it ready to prove another theorem.
    """
    tlist0 = tl.tlist0
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    tlist0.data = []
    n = len(tlist1.data)
    for i in range(0, n):
        del tlist1.data[n - i - 1]
    tlist1.line = 0
    n = len(tlist2.data)
    for i in range(0, n):
        del tlist2.data[n - i - 1]
    tlist2.line = 0
    tl.vars = dict()
    tl.tars = dict()
    tl.constraints = dict()
    tl.constraints_processed = (0, 0, 0)
    tl.sorts_processed = (0, 0, 0)
    tl.tlist1.dep = dict()
    tl.loaded_theorem = None
    tl.focus = tl.tlist0
    tl.moves = []
    tl.unifications = []
    tl.unification_count = []

def filter_library(screen, tl, library, tags):
    tags = canonicalise_tags(tags) # deal with constraint shorthands
    taglist = tags_to_list(tags)
    print("taglist:"+str(taglist))
    filtered_titles = []
    title = library.readline()
    while title: # check for EOF
        library.readline() # skip constants for now
        library.readline() # skip terms for now
        libtaglist = tags_to_list(library.readline()[0:-1])
        if all(elem in libtaglist for elem in taglist):
            filtered_titles.append((library.tell(), title[7:-1]))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    return filtered_titles

def library_load(screen, tl, library, filepos):
    """
    Given an open library file (library) and a fileposition (filepos), load the
    theorem/definition at the given position into the tableau. The function
    returns a pair, (dirty1, dirty2) which are lines of the tableau that were
    affected in the hypothesis and target panes respectively. The caller is
    responsible for updating these in the interface, along with the quantifier
    zone, which is assumed to always be updated.
    """
    dirty1 = []
    dirty2 = []
    library.seek(filepos)
    tlist0 = tl.tlist0.data
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    fstr = library.readline()
    if fstr != '------------------------------\n':
        stmt = to_ast(screen, fstr[0:-1])
        append_tree(tlist0, stmt, None)
        library.readline()
        fstr = library.readline()
        while fstr != '------------------------------\n':
            stmt = to_ast(screen, fstr[0:-1])
            append_tree(tlist1, stmt, dirty1)
            fstr = library.readline()
        fstr = library.readline()
        while fstr != '\n':
            stmt = to_ast(screen, fstr[0:-1])
            append_tree(tlist2, stmt, dirty2)
            fstr = library.readline()
    else:
        library.readline()
        library.readline()
        fstr = library.readline()
        while fstr != '\n':
            stmt = to_ast(screen, fstr[0:-1])
            append_tree(tlist2, stmt, dirty2)
            fstr = library.readline()
    return dirty1, dirty2

def library_import(screen, tl, library, filepos):
    """
    Given an open library file (library) and a fileposition (filepos), load the
    theorem/definition at the given position into the hypotheses. The function
    returns True if the operation was successful, otherwise False. In theory,
    the function should not fail.
    """
    library.seek(filepos)
    fstr = library.readline()
    hyps = []
    tars = []
    if fstr != '------------------------------\n':
        tree = to_ast(screen, fstr[0:-1])
        t = tree
        while t.left:
            t = t.left
        library.readline()
        fstr = library.readline()
        while fstr != '------------------------------\n':
            hyps.append(to_ast(screen, fstr[0:-1]))
            fstr = library.readline()
        fstr = library.readline()
        while fstr != '\n':
            tars.append(to_ast(screen, fstr[0:-1]))
            fstr = library.readline()
        if hyps:
            jhyps = hyps[0]
            for node in hyps[1:]:
                jhyps = AndNode(jhyps, node)
        jtars = tars[0]
        for i in tars[1:]:
            jtars = AndNode(jtars, i)
        if hyps:
            t.left = ImpliesNode(jhyps, jtars)
        else:
            t.left = jtars
    else:
        library.readline()
        library.readline()
        fstr = library.readline()
        while fstr != '\n':
            tars.append(to_ast(screen, fstr[0:-1]))
            fstr = library.readline()
        tree = tars[0]
        for i in tars[1:]:
            tree = AndNode(tree, i)
    tlist1 = tl.tlist1.data
    stmt, _ = relabel(screen, tl, [], tree)
    ok = process_constraints(screen, tl, stmt, tl.constraints)
    if ok:
        append_tree(tlist1, stmt, None)
    return ok

def fake_import(screen, tl, library, filepos):
    """
    Fakes the import of a library result. Nothing is added to the tableau but
    instead the function returns the lines of the tableau that would result as
    a list. However, no renaming is done, no skolemization and no creation of
    metavariables. However, the function does split apart iff statements and
    all the usual splitting of implications is done just as would result from
    cleanup moves from a real import. The first two returned values are any
    binders for the quantifier zone and any predicates P from theorems of the
    form P => (Q iff R), the remaining iff being split as normal in the list
    of theorems that results. Equalities are stated in both directions.
    """
    library.seek(filepos)
    fstr = library.readline()
    hyps = []
    tars = []
    if fstr != '------------------------------\n':
        tree = to_ast(screen, fstr[0:-1])
        t = tree
        while t.left:
            t = t.left
        library.readline()
        fstr = library.readline()
        while fstr != '------------------------------\n':
            hyps.append(to_ast(screen, fstr[0:-1]))
            fstr = library.readline()
        fstr = library.readline()
        while fstr != '\n':
            tars.append(to_ast(screen, fstr[0:-1]))
            fstr = library.readline()
        if hyps:
            jhyps = hyps[0]
            for node in hyps[1:]:
                jhyps = AndNode(jhyps, node)
        jtars = tars[0]
        for i in tars[1:]:
            jtars = AndNode(jtars, i)
        if hyps:
            t.left = ImpliesNode(jhyps, jtars)
        else:
            t.left = jtars
    else:
        library.readline()
        library.readline()
        fstr = library.readline()
        while fstr != '\n':
            tars.append(to_ast(screen, fstr[0:-1]))
            fstr = library.readline()
        tree = tars[0]
        for i in tars[1:]:
            tree = AndNode(tree, i)
    # peel any binders
    if (isinstance(tree, ForallNode) and not isinstance(tree.left, ImpliesNode)) or \
        isinstance(tree, ExistsNode):
        qz = tree
        while (isinstance(tree.left, ForallNode) and not isinstance(tree.left.left, ImpliesNode)) or \
               isinstance(tree.left, ExistsNode):
            tree = tree.left
        t = tree.left
        tree.left = None
        tree = t
    else:
        qz = None
    tpred = None
    impls = []
    if isinstance(tree, ForallNode):
        impls.append(tree)
    elif isinstance(tree, IffNode):
        # split iff statement or P => (Q iff R)
        impls.append(ImpliesNode(tree.left, tree.right, True))
        impls.append(ImpliesNode(tree.right, tree.left, True))
    elif isinstance(tree, ImpliesNode) and isinstance(tree.right, IffNode):
        tpred = tree.left
        impls.append(ImpliesNode(tree.right.left, tree.right.right, True))
        impls.append(ImpliesNode(tree.right.right, tree.right.left, True))
    elif isinstance(tree, EqNode):
        impls.append(tree)
    elif isinstance(tree, ImpliesNode) and isinstance(tree.right, EqNode):
        tpred = tree.left
        impls.append(tree.right)
    else:
        impls.append(tree)
    i = 0
    while i < len(impls):
        if isinstance(impls[i], ForallNode):
            impls[i] = impls[i].left
        else:
            if isinstance(impls[i], ImpliesNode) and isinstance(impls[i].left, OrNode):
                var1 = vars_used(screen, tl, impls[i].left.left)
                var2 = vars_used(screen, tl, impls[i].left.right)
                var = vars_used(screen, tl, impls[i].right)
                if set(var).issubset(var1) and set(var).issubset(var2):
                    P = impls[i].left.left
                    Q = impls[i].left.right
                    R = impls[i].right
                    impls[i] = ImpliesNode(P, R, impls[i].iff)
                    impls.append(ImpliesNode(Q, R, impls[i].iff))
            if isinstance(impls[i], ImpliesNode) and isinstance(impls[i].right, AndNode):
                impls.append(ImpliesNode(impls[i].left, impls[i].right.left, impls[i].iff))
                impls[i] = ImpliesNode(impls[i].left, impls[i].right.right, impls[i].iff)
        i += 1
    return qz, tpred, impls

def library_export(screen, tl, library, title, tags):
    """
    Given a library file (library) open for appending, a title string and a
    string which is a comma separated list of tags, write the current tableau
    to the library as a theorem/definition.
    """
    tlist0 = tl.tlist0.data
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    c0 = get_constants(screen, tl, tlist0[0]) 
    if len(tlist1) == 0 and len(tlist2) == 1 and \
       (isinstance(tlist2[0], IffNode) or isinstance(tlist2[0], EqNode)):
        is_iff = True
        c1 = get_constants(screen, tl, tlist2[0].left)
        c2 = get_constants(screen, tl, tlist2[0].right)
    else:
        is_iff = False
        c1 = merge_lists([get_constants(screen, tl, v) for v in tlist1])
        c2 = merge_lists([get_constants(screen, tl, v) for v in tlist2])
    consts = "["+str(is_iff)+", "+str(c0)+", "+str(c1)+", "+str(c2)+"]\n"
    library.write(title+"\n")
    library.write(consts+"\n")
    library.write(tags+"\n")
    qz_written = False
    if tlist0:
        library.write(repr(tlist0[0]))
        qz_written = True
    for hyp in tlist1:
        while isinstance(hyp, ExistsNode):
            if qz_written:
                library.write(" ")
            library.write(repr(ExistsNode(hyp.var, None)))
            hyp = hyp.left
            qz_written = True
    for tar in tlist2:
        while isinstance(tar, ForallNode):
            if qz_written:
                library.write(" ")
            library.write(repr(ForallNode(tar.var, None)))
            tar = tar.left
            qz_written = True
    if qz_written:
        library.write("\n")
    library.write("------------------------------\n")
    for hyp in tlist1:
        while isinstance(hyp, ExistsNode):
            hyp = hyp.left
        library.write(repr(hyp)+"\n")
    library.write("------------------------------\n")
    for tar in tlist2:
        while isinstance(tar, ForallNode):
            tar = tar.left
        library.write(repr(tar)+"\n")
    library.write("\n")

def cleanup(screen, tl, ttree):
    """
    Automated cleanup moves. This applies numerous moves that the user will
    essentially always want to do. This is applied automatically after every
    move to make less work for the user. The moves applied are the following:
      * skolemization of existentially bound variables
      * creation of metavariables
      * moving outside binders on hypotheses/targets to the quantifier zone
    For hypotheses we perform the following moves:
      * convert P \vee P to P
      * convert ¬P \vee Q to P => Q
      * convert P \iff Q to P => Q and Q => P
      * replace P \wedge P with P
      * convert P \wedge Q to P and Q
      * convert ¬(P \implies Q) to P and ¬Q
      * convert (P \vee Q) => R to P => R and Q => R if such implications
        would not introduce new metavariables
      * convert P => (Q \wedge R) to P => Q and P => R
    For targets we perform the following moves:
      * for P \vee Q introduce a hypothesis ¬P and replace the implication with Q,
        with appropriate dependency tracking
      * for P => Q introduce a hypothesis P and replace the implication with Q, with
        appropriate dependency tracking
      * convert P \wedge P to P
      * convert P \wedge Q to P and Q
      * convert ¬(P \implies Q) to P and ¬Q
    These are applied repeatedly until no further automated moves are possible.
    """
    tl0 = tl.tlist0.data # quantifier zone
    tl1 = tl.tlist1.data # hypotheses
    tl2 = tl.tlist2.data # targets
    dirty1 = []
    dirty2 = []
    deps = []
    sk = []
    qz = []
    mv = []
    if tl0:
        sq, deps, sk, ex = skolemize_quantifiers(tl0[0], deps, sk, [])
        qzext = []
        if len(ex) > 0: # constraint of new skolem variable will need to be recomputed
           tl.constraints_processed = (0, 0, 0)
           tl.sorts_processed = (0, 0, 0)
        for i in range(len(ex)):
            n = sk[i][1] # number of dependencies
            domain_constraints = [v.var.constraint if isinstance(v, ForallNode) else v.constraint for v in deps[0:n]]
            if len(domain_constraints) > 1:
                fn_constraint = FunctionConstraint(DomainTuple(domain_constraints), SetOfNode(ex[i].constraint))
            elif len(domain_constraints) == 1:
                fn_constraint = FunctionConstraint(domain_constraints[0], SetOfNode(ex[i].constraint))
            else:
                fn_constraint = FunctionConstraint(None, SetOfNode(ex[i].constraint))
            var = VarNode(ex[i].name(), fn_constraint)
            var.skolemized = True # make sure we don't skolemize it again
            qzext.append(ExistsNode(var, None))
        if qzext:
            root = qzext[0]
            t = root
            t.left = None
            for i in range(1, len(qzext)):
                v = qzext[i]
                v.left = None
                t.left = v
                t = t.left
            if sq:
                t.left = sq
            tl.tlist0.data[0] = root
        else:
            tl.tlist0.data[0] = sq
        
    d = len(deps)
    s = len(sk)
    m = len(mv)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()
    
    depmin = d # avoid dependencies on original qz variables

    if tl0: # process constraints of variables in qz
        tree = tl0[0]
        while tree:
            tree.var.constraint = skolemize_statement(screen, tree.var.constraint, deps, depmin, sk, qz, mv, True, False)
            rollback()
            tree = tree.left

    hyps_done = False
    tars_done = False
    i = 0
    j = 0
    while not hyps_done or not tars_done:
        if not hyps_done:
            hyps_done = True
            while i < len(tl1):
                oldtli = str(tl1[i])
                tl1[i] = skolemize_statement(screen, tl1[i], deps, depmin, sk, qz, mv, False, False)
                if str(tl1[i]) != oldtli and i not in dirty1:
                    dirty1.append(i)
                rollback()
                t = tl1[i]
                if isinstance(t, ExistsNode) or isinstance(t, ForallNode):
                    while isinstance(t, ExistsNode) or isinstance(t, ForallNode) \
                           and not isinstance(t.left, OrNode):
                        t = t.left
                    if isinstance(t.left, OrNode):
                        t.left = ImpliesNode(complement_tree(t.left.left), t.left.right)
                        if isinstance(t.left.left, NotNode) and isinstance(t.left.right, NotNode):
                            temp = t.left.left.left
                            t.left.left = t.left.right.left
                            t.left.right = temp
                        dirty1.append(i)
                if isinstance(tl1[i], OrNode):
                    # First check we don't have P \vee P
                    unifies, assign, macros = unify(screen, tl, tl1[i].left, tl1[i].right)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if unifies and not assign:
                        replace_tree(tl1, i, tl1[i].left, dirty1)
                    else:
                        stmt = ImpliesNode(complement_tree(tl1[i].left), tl1[i].right)
                        if isinstance(stmt.left, NotNode) and isinstance(stmt.right, NotNode):
                            temp = stmt.left.left
                            stmt.left = stmt.right.left
                            stmt.right = temp
                        replace_tree(tl1, i, stmt, dirty1)
                if isinstance(tl1[i], IffNode):
                    tl1[i] = ImpliesNode(tl1[i].left, tl1[i].right)
                    impl = ImpliesNode(deepcopy(tl1[i].right), deepcopy(tl1[i].left))
                    append_tree(tl1, impl, dirty1)
                    tl.tlist1.dep[len(tl1) - 1] = tl.tlist1.dependency(i)
                    stmt = skolemize_statement(screen, tl1[i], deps, depmin, sk, qz, mv, False)
                    replace_tree(tl1, i, stmt, dirty1)
                    rollback()
                while isinstance(tl1[i], AndNode):
                    # First check we don't have P \wedge P
                    if same_tree(screen, tl, tl1[i].left, tl1[i].right):
                        replace_tree(tl1, i, tl1[i].left, dirty1)
                    else:
                        append_tree(tl1, tl1[i].right, dirty1)
                        replace_tree(tl1, i, tl1[i].left, dirty1)
                        n = len(tl1) - 1
                        tl.tlist1.dep[n] = tl.tlist1.dependency(i)
                        duplicate_move(screen, tl, n, i)
                        mark_shared(tl1[i], tl1[n])
                if isinstance(tl1[i], NotNode) and isinstance(tl1[i].left, ImpliesNode):
                    append_tree(tl1, complement_tree(tl1[i].left.right), dirty1)
                    replace_tree(tl1, i, tl1[i].left.left, dirty1)
                    n = len(tl1) - 1
                    tl.tlist1.dep[n] = tl.tlist1.dependency(i)
                    duplicate_move(screen, tl, n, i)
                    mark_shared(tl1[i], tl1[n])
                if isinstance(tl1[i], ImpliesNode) and isinstance(tl1[i].left, OrNode):
                    var1 = metavars_used(tl1[i].left.left)
                    var2 = metavars_used(tl1[i].left.right)
                    var = metavars_used(tl1[i].right)
                    # make sure no additional metavars are introduced
                    if set(var).issubset(var1) and set(var).issubset(var2):
                        P = tl1[i].left.left
                        Q = tl1[i].left.right
                        R = tl1[i].right
                        # first check we don't have P => P
                        if same_tree(screen, tl, P, R):
                            replace_tree(tl1, i, ImpliesNode(Q, R), dirty1)
                        else:
                            replace_tree(tl1, i, ImpliesNode(P, R), dirty1)
                            # first check we don't have Q => Q
                            if not same_tree(screen, tl, Q, R):
                                append_tree(tl1, ImpliesNode(Q, deepcopy(R)), dirty1)
                                n = len(tl1) - 1
                                tl.tlist1.dep[n] = tl.tlist1.dependency(i)
                                duplicate_move(screen, tl, n, i)
                                mark_shared(tl1[i], tl1[n])
                if isinstance(tl1[i], ImpliesNode) and isinstance(tl1[i].right, AndNode):
                    P = tl1[i].left
                    Q = tl1[i].right.left
                    R = tl1[i].right.right
                    # first check we don't have P => P
                    if same_tree(screen, tl, P, R):
                        replace_tree(tl1, i, ImpliesNode(P, Q), dirty1)
                    else:
                        replace_tree(tl1, i, ImpliesNode(P, R), dirty1)
                        # first check we don't have P => P
                        if not same_tree(screen, tl, P, Q):
                            append_tree(tl1, ImpliesNode(deepcopy(P), Q), dirty1)
                            n = len(tl1) - 1
                            tl.tlist1.dep[n] = tl.tlist1.dependency(i)
                            duplicate_move(screen, tl, n, i)
                            mark_shared(tl1[i], tl1[n])
                i += 1
                while len(mv) > m:
                    mv.pop()
        if not tars_done:
            tars_done = True
            while j < len(tl2):
                oldtlj = str(tl2[j])
                tl2[j] = skolemize_statement(screen, tl2[j], deps, depmin, sk, qz, mv, True, False, True)
                if str(tl2[j]) != oldtlj and j not in dirty2:
                    dirty2.append(j)
                rollback()
                if isinstance(tl2[j], OrNode):
                    append_tree(tl1, complement_tree(tl2[j].left), dirty1)
                    hyps_done = False
                    replace_tree(tl2, j, tl2[j].right, dirty2)
                    n = len(tl1) - 1
                    tl.tlist1.dep[n] = [j]
                    mark_shared(tl2[j], tl1[n])
                if isinstance(tl2[j], ImpliesNode):
                    # can't relabel or metavar dependencies between existing targets broken
                    # left = relabel(screen, tl, [], tl2[j].left, tl.vars, True)
                    left = tl2[j].left
                    append_tree(tl1, left, dirty1)
                    hyps_done = False
                    # can't relabel or metavar dependencies between existing targets broken
                    # right = relabel(screen, tl, [], tl2[j].right, tl.vars, True)
                    right = tl2[j].right
                    replace_tree(tl2, j, right, dirty2)
                    n = len(tl1) - 1
                    tl.tlist1.dep[n] = [j]
                    mark_shared(tl2[j], tl1[n])
                while isinstance(tl2[j], AndNode):
                    # First check we don't have P \wedge P
                    unifies, assign, macros = unify(screen, tl, tl2[j].left, tl2[j].right)
                    unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                    if unifies and not assign:
                        replace_tree(tl2, j, tl2[j].left, dirty2)
                    else:
                        append_tree(tl2, tl2[j].right, dirty2)
                        replace_tree(tl2, j, tl2[j].left, dirty2)
                        n = len(tl2) - 1
                        add_sibling(screen, tl, ttree, j, n)
                        mark_shared(tl2[j], tl2[n])
                if isinstance(tl2[j], NotNode) and isinstance(tl2[j].left, ImpliesNode):
                    append_tree(tl2, complement_tree(tl2[j].left.right), dirty2)
                    replace_tree(tl2, j, tl2[j].left.left, dirty2)
                    n = len(tl2) - 1
                    add_sibling(screen, tl, ttree, j, n)
                    mark_shared(tl2[j], tl2[n])
                if not isinstance(tl2[j], ForallNode) and not isinstance(tl2[j], ExistsNode) \
                   and not isinstance(tl2[j], ImpliesNode):
                    j += 1
                while len(mv) > m:
                    mv.pop()

    if qz:
        tl.constraints_processed = (0, 0, 0)
        tl.sorts_processed = (0, 0, 0)
        if tl0:
            t = tl0[0]
            while t.left:
                t = t.left
            r = range(0, len(qz))
        else:
            tl0.append(qz[0])
            t = qz[0]
            r = range(1, len(qz))
        for i in r:
            t.left = qz[i]
            t = t.left
        t.left = None

    return dirty1, dirty2