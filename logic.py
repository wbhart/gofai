from utility import unquantify, relabel, append_tree, add_descendant, \
     target_compatible, complement_tree
from unification import check_macros, unify, substitute
from copy import deepcopy
from nodes import AndNode, ImpliesNode, LRNode, LeafNode, ForallNode, \
     TupleNode, FnApplNode

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

    tree1 = tlist1.data[line1]
    tree1, univs = unquantify(screen, tree1, False) # remove quantifiers by taking temporary metavars
    
    if forward:
        qP1, u = unquantify(screen, tree1.left, True)
    else:
        tree1 = relabel(screen, tl, univs, tree1, True)
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
        unifies, assign, macros = unify(screen, tl, qP1, complement_tree(relabel(screen, tl, [], deepcopy(qP2.left), temp=True)))
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
        if unifies:
            # temporary relabelling
            unifies, assign, macros = unify(screen, tl, qP1, relabel(screen, tl, [], deepcopy(qP2.right), temp=True), assign)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    else:
        unifies, assign, macros = unify(screen, tl, qP1, qP2)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    if not unifies:
        return False # fail: predicate does not match implication
    stmt = substitute(deepcopy(conseq), assign)
    if forward:
        stmt = relabel(screen, tl, univs, stmt, True)
        append_tree(screen.pad1, tlist1.data, stmt)
        tlist1.dep[len(tlist1.data) - 1] = dep
    else:
        if line2 in tl.tars: # we already reasoned from this target
            stmt = complement_tree(stmt)
            append_tree(screen.pad1, tlist1.data, stmt) # add negation to hypotheses
            tlist1.dep[len(tlist1.data) - 1] = dep
        else:
            append_tree(screen.pad2, tlist2.data, stmt)
            add_descendant(ttree, line2, len(tlist2.data) - 1)
            tl.tars[line2] = True
    return True

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

    tree1 = tlist1.data[line1]
    tree1, univs = unquantify(screen, tree1, False) # remove quantifiers by taking temporary metavars
    
    if forward:
        qP1, u = unquantify(screen, tree1.right, False)
    else:
        tree1 = relabel(screen, tl, univs, tree1, True)
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
        unifies, assign, macros = unify(screen, tl, qP1, complement_tree(relabel(screen, tl, [], deepcopy(qP2.left), temp=True)))
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
        if unifies:
            # temporary relabelling
            unifies, assign, macros = unify(screen, tl, qP1, relabel(screen, tl, [], deepcopy(qP2.right), temp=True), assign)
            unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    else:
        unifies, assign, macros = unify(screen, tl, qP1, qP2)
        unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
    if not unifies:
        return False # fail: predicate does not match implication
    stmt = complement_tree(substitute(deepcopy(conseq), assign))
    if forward:
        stmt = relabel(screen, tl, univs, stmt, True)
        append_tree(screen.pad1, tlist1.data, stmt)
        tlist1.dep[len(tlist1.data) - 1] = dep
    else:
        if line2 in tl.tars: # we already reasoned from this target
            stmt = complement_tree(stmt)
            append_tree(screen.pad1, tlist1.data, stmt) # add negation to hypotheses
            tlist1.dep[len(tlist1.data) - 1] = dep
        else:
            append_tree(screen.pad2, tlist2.data, stmt)
            add_descendant(ttree, line2, len(tlist2.data) - 1)
            tl.tars[line2] = True
    return True

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
                unifies, assign, macros = unify(screen, tl, subst.left, tree)
                unifies = unifies and check_macros(screen, tl, macros, assign, tl.tlist0.data)
                if not unifies:
                    unifies, assign, macros = unify(screen, tl, subst.right, tree)
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
        if is_hyp:
            tl.tlist1.data[line2] = tree
        else:
            tl.tlist2.data[line2] = tree
    return found