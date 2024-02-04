from nodes import ForallNode, ExistsNode, FnApplNode, VarNode, SetBuilderNode, \
     LRNode, TupleNode, SymbolNode, NotNode, EqNode, NeqNode, GtNode, LtNode, \
     LeqNode, GeqNode, AndNode, OrNode, IffNode, ImpliesNode, UnionNode, \
     IntersectNode, DiffNode, CartesianNode, SetOfNode, NaturalNode, ExpNode, \
     CircNode, TupleComponentNode, PowerSetNode, AddNode, SubNode, MulNode, \
     DivNode, SubsetneqNode, SubseteqNode, SupsetneqNode, SupseteqNode, \
     AbsNode, NegNode, ElemNode, BoolNode, DeadNode, LambdaNode, LeafNode
from sorts import SetSort, TupleSort, FunctionConstraint, DomainTuple, \
     CartesianConstraint, Universum, NumberSort, PredSort, Sort
from typeclass import CompleteValuedFieldClass, CompleteOrderedValuedFieldClass, \
     FieldClass, OrderedRingClass, OrderedSemiringClass, PosetClass, MonoidClass, \
     SemiringClass, ValuedFieldClass
from copy import deepcopy, copy
from heapq import merge  

system_unary_functions = ['complement', 'universe']
system_binary_functions = ['min', 'max']
system_predicates = ['is_bounded', 'is_upper_bound', 'is_lower_bound', 'is_supremum', \
                     'is_infimum', 'is_pair', 'is_function', 'is_injective', \
                     'is_surjective', 'is_bijective']

def is_expression(tree):
    if isinstance(tree, VarNode) or isinstance(tree, NaturalNode) \
       or isinstance(tree, FnApplNode) or isinstance(tree, ExpNode) \
       or isinstance(tree, AddNode) or isinstance(tree, SubNode) \
       or isinstance(tree, MulNode) or isinstance(tree, DivNode) \
       or isinstance(tree, IntersectNode) or isinstance(tree, UnionNode) \
       or isinstance(tree, DiffNode) or isinstance(tree, PowerSetNode) \
       or isinstance(tree, SymbolNode) or isinstance(tree, LambdaNode) \
       or isinstance(tree, TupleComponentNode) or isinstance(tree, Sort):
        return True
    else:
        return True

def is_predicate(tree):
    if isinstance(tree, AndNode) or isinstance(tree, OrNode) \
       or isinstance(tree, ElemNode) or isinstance(tree, EqNode) \
       or isinstance(tree, NeqNode) or isinstance(tree, LtNode) \
       or isinstance(tree, GtNode) or isinstance(tree, GeqNode) \
       or isinstance(tree, LeqNode) or isinstance(tree, SubseteqNode) \
       or isinstance(tree, SubsetneqNode) or isinstance(tree, SupseteqNode) \
       or isinstance(tree, SupsetneqNode) or isinstance(tree, ImpliesNode) \
       or isinstance(tree, IffNode) or isinstance(tree, NotNode) \
       or isinstance(tree, ForallNode) or isinstance(tree, ExistsNode) \
       or isinstance(tree, BoolNode):
        return True
    else:
        return False

def universe(tree, qz):
    """
    Given a parse tree of a set object, compute the universe of the set. This
    function is used to fill in the universe macro for set objects.
    """
    if isinstance(tree, VarNode):
        t = get_constraint(tree, qz)
        return t.sort
    elif isinstance(tree, UnionNode) or isinstance(tree, IntersectNode) or \
         isinstance(tree, DiffNode):
        return universe(tree.left, qz)
    elif isinstance(tree, CartesianNode):
        return TupleSort([universe(tree.left, qz), universe(tree.right, qz)])
    elif isinstance(tree, FnApplNode) and tree.name() == 'complement':
        return universe(tree.args[0], qz)
    elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset':
        return tree.constraint
    elif isinstance(tree, PowerSetNode):
        return PowerSetNode(universe(tree.left, qz))
    else:
        return None # no universe

def domain(tree, qz):
    """
    Given the parse tree for a variable with function constraint, return the
    domain of the function. This function is used to fill in the domain macro
    for function objects.
    """
    if isinstance(tree, VarNode):
        if tree.is_metavar:
            return None
        else:
            fn_constraint = get_constraint(tree, qz)
            return fn_constraint.domain
    else:
        return None # no domain

def codomain(tree, qz):
    """
    Given the parse tree for a variable with function constraint, return the
    codomain of the function. This function is used to fill in the codomain
    macro for function objects.
    """
    if isinstance(tree, VarNode):
        if tree.is_metavar:
            return None
        else:
            fn_constraint = get_constraint(tree, qz)
            return fn_constraint.codomain
    else:
        return None # no codomain

def sort_to_set(tree, outer=True):
    """
    Convert a sort to a set of all elements of the type.
    """
    if isinstance(tree, VarNode):
        return SetOfNode(tree)
    elif isinstance(tree, SetSort):
        return PowerSetNode(sort_to_set(tree.sort, False))
    elif isinstance(tree, TupleSort) and len(tree.sorts) == 2:
        return CartesianNode(sort_to_set(tree.sorts[0], False), sort_to_set(tree.sorts[0], False))
    else:
        raise Exception(str(type(tree)))

def subst(tree1, var, tree2):
    if tree1 == None:
        return tree1
    if isinstance(tree1, ForallNode) or isinstance(tree1, ExistsNode):
        tree1.var.constraint = subst(tree1.var.constraint, var, tree2)
        if isinstance(tree1.var.constraint, TupleSort):
            tree1.var.constraint = CartesianConstraint(tree1.var.constraint.sorts)
        tree1.left = subst(tree1.left, var, tree2)
        return tree1
    if isinstance(tree1, VarNode):
        tree1.constraint = subst(tree1.constraint, var, tree2)
        if tree1.name() == var.name():
            return deepcopy(tree2)
        else:
            return tree1
    elif isinstance(tree1, TupleComponentNode):
        # special hack to expand (a, b)[0] as function application
        if isinstance(tree1.left, VarNode) and tree1.left.name() == var.name() \
             and isinstance(tree2, TupleNode):
            n = tree1.right.value
            if n >= len(tree2.args):
                raise Exception("Invalid indexing in tuple")
            return tree2.args[n]
        p = deepcopy(tree1)
        p.left = subst(p.left, var, tree2)
        return p
    elif isinstance(tree1, FnApplNode):
        if tree1.name() == var.name() and is_predicate(tree2):
            p = deepcopy(tree2)
            for i in range(0, len(tree1.args)):
                p = subst(p, var.args[i], tree1.args[i])
            return p
        p = deepcopy(tree1)
        p.var = subst(p.var, var, tree2)
        if not isinstance(p.var, VarNode) and not isinstance(p.var, FnApplNode):
            p.is_metavar = False
        elif tree1.name() == var.name(): # we did substitution
            p.is_metavar = tree2.is_metavar
        for i in range(0, len(p.args)):
            p.args[i] = subst(p.args[i], var, tree2)
        return p
    elif isinstance(tree1, TupleNode):
        args = [subst(t, var, tree2) for t in tree1.args]
        return TupleNode(args)
    elif isinstance(tree1, SetOfNode):
        if isinstance(tree1.left, VarNode) and tree1.left.name() == var.name():
            tree1.left.constraint = subst(tree1.left.constraint, var, tree2)
            return sort_to_set(deepcopy(tree2))
        else:
            tree1.left = subst(tree1.left, var, tree2)
            return tree1
    elif isinstance(tree1, LRNode):
        tree1.left = subst(tree1.left, var, tree2)
        tree1.right = subst(tree1.right, var, tree2)
        return tree1
    elif isinstance(tree1, SymbolNode) and tree1.name() == '\\emptyset':
        tree1.constraint = subst(tree1.constraint, var, tree2)
        return tree1
    elif isinstance(tree1, SetSort):
        if tree1.sort != tree1:
            tree1.sort = subst(tree1.sort, var, tree2)
        return tree1
    elif isinstance(tree1, TupleSort):
        for i in range(len(tree1.sorts)):
            tree1.sorts[i] = subst(tree1.sorts[i], var, tree2)
        return tree1
    elif isinstance(tree1, CartesianConstraint):
        for i in range(len(tree1.sorts)):
            tree1.sorts[i] = subst(tree1.sorts[i], var, tree2)
        return tree1
    else:
        return tree1

def make_substitution(assign1, assign2):
    (var1, expr1) = assign1
    (var2, expr2) = assign2

    var1 = subst(deepcopy(var1), var2, expr2) # in case it is a function
    return (var1, subst(deepcopy(expr1), var2, expr2))

def substitute(tree, assign):
   for (var, val) in assign:
       tree = subst(tree, var, val)
   return tree

def complement_tree(tree):
    """
    Return the complement of a given statment, simplifying where possible.
    Used by modus tollens.
    """ 
    def complement(tree):
        if isinstance(tree, ForallNode):
            return ExistsNode(tree.var, complement(tree.left))
        elif isinstance(tree, ExistsNode):
            return ForallNode(tree.var, complement(tree.left))
        elif isinstance(tree, EqNode):
            return NeqNode(tree.left, tree.right)
        elif isinstance(tree, NeqNode):
            return EqNode(tree.left, tree.right)
        elif isinstance(tree, LtNode):
            return GeqNode(tree.left, tree.right)
        elif isinstance(tree, GtNode):
            return LeqNode(tree.left, tree.right)
        elif isinstance(tree, LeqNode):
            return GtNode(tree.left, tree.right)
        elif isinstance(tree, GeqNode):
            return LtNode(tree.left, tree.right)
        elif isinstance(tree, AndNode):
            return OrNode(complement(tree.left), complement(tree.right))
        elif isinstance(tree, OrNode):
            return AndNode(complement(tree.left), complement(tree.right))
        elif isinstance(tree, ImpliesNode):
            return AndNode(tree.left, complement(tree.right))
        elif isinstance(tree, NotNode):
            return tree.left
        else:
            return NotNode(tree)

    return complement(deepcopy(tree))

def dangling_to_left(tree, dangling):
    """
    If there are only dangling variables on the right of the tree, switch the
    left and right sides of the tree so dangling vars are on the left.
    """
    var1 = vars_used(None, None, tree.left, True)

    if not any(v in dangling for v in var1):
        var2 = vars_used(None, None, tree.right, True)
    
        if any(v in dangling for v in var2):
            t = tree.left
            tree.left = tree.right
            tree.right = t

def find_dangling_vars(hyps, hyplist, tars, tarlist):
    duplicates = [] # variables that are duplicated
    dangling = [] # variables that only occur once

    for i in hyplist:
        var_list = vars_used(None, None, hyps[i], True)
        
        for var in var_list:
            if var not in duplicates:
                if var in dangling:
                    dangling.remove(var)
                    duplicates.append(var)
                else:
                    dangling.append(var)

    for i in tarlist:
        var_list = vars_used(None, None, tars[i], True)
        
        for var in var_list:
            if var not in duplicates:
                if var in dangling:
                    dangling.remove(var)
                    duplicates.append(var)
                else:
                    dangling.append(var)

    return dangling
    
def unquantify(screen, tree, positive):
    """
    Remove forall quantifiers from a statement, returning a deepcopy of the
    matrix and a list of the quantifiers removed (now unlinked).

    The function should be called with positive=True if the statement is
    from the targets, else False.
    """
    tree = deepcopy(tree)
    mv = []
    univs = []
    while isinstance(tree, ForallNode):
        mv.append(tree.var.name())
        t = tree
        tree = tree.left
        t.left = None
        univs.append(t)
    tree = skolemize_statement(screen, tree, [], 0, [], [], mv, positive)
    return tree, univs

def relabel_varname(name, var_dict):
    """
    Return a new name for the variable with the given name. A dictionary of
    past renaming is also supplied.

    First, any current subscript is removed and a new subscript (greater than
    any previously used for this variable) is appended.
    """
    sp = name.split("_")
    if sp.pop().isdigit():
        name = '_'.join(sp)
    if name in var_dict:
        subscript = var_dict[name] + 1
    else:
        subscript = 0
    var_dict[name] = subscript
    return name+'_'+str(subscript)

def new_variable(screen, tl, string):
    """
    Given a string, return a variable name which has not been used, based on
    that string. At present, it will simply add a subscript to the name and
    prepend an underscore. These variables are intended to be used internally.
    """
    var_dict = tl.vars
    
    return relabel_varname('_'+string, var_dict)

    
def qz_copy_var(screen, tl, extras, name, new_name, copied, assign=None):
    """
    Make a copy, in the quantifier zone of the tableau, of the variable with
    the given name. The copy will be given the new_name specified, but type
    information and any flags attached to the variable will be kept the same.

    In addition, a list of existential or universal quantifiers may be
    specified which are missing from the quantifier zone, but which should be
    added (after renaming) if their name is the one specified.

    The function is safe to call multiple times with the same name, as it
    ignores variables it has already copied under the new name supplied.

    The new variable will use the supplied constraint instead of the existing
    one.
    """
    node_to_copy = None
    qz = tl.tlist0.data[0] if tl.tlist0.data else None
    tree = qz

    for v in extras: # extra variables to rename, from unquantify
       if isinstance(v, ExistsNode) or isinstance(v, ForallNode):
          if v.var.name() == name: # found the relevant variable
              node_to_copy = v

    if tree == None:
       if node_to_copy != None:
          new_node = copy(node_to_copy)
          new_node.var = deepcopy(new_node.var)
          if isinstance(new_node.var, VarNode):
              new_node.var._name = new_name # rename
          elif isinstance(new_node.var, FnApplNode): # TODO : not sure if this is used any more
              new_node.var.var._name = new_name # rename
          new_node.left = None
          if assign:
              new_node = substitute(new_node, assign)
          tl.tlist0.data.append(new_node)
          copied.append(new_node)
          return

    while tree != None:
       if isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
          if tree.var.name() == new_name:
              return
          if tree.var.name() == name: # found the relevant variable
              node_to_copy = tree
       if tree.left == None and node_to_copy != None: # this is the last node, make copy
          new_node = copy(node_to_copy)
          new_node.var = deepcopy(new_node.var)
          if isinstance(new_node.var, VarNode):
              new_node.var._name = new_name # rename
          elif isinstance(new_node.var, FnApplNode): # TODO : not sure if this is used any more
              new_node.var.var._name = new_name # rename
          new_node.left = None
          tree.left = new_node 
          if assign:
              new_node = substitute(new_node, assign)
          copied.append(new_node)  
       tree = tree.left
       
def relabel(screen, tl, extras, tree, update_qz=False, temp=False, assign=None):
    """
    Relabel inplace all metavars in the given tree. This is the primary
    mechanism to prevent variable capture.

    If temporary renaming is required so that the dictionary of previous
    renames is not altered, specify temp=True.

    If update_qz=True the function makes a copy of any renamed variable
    in the quantifier zone, retaining the existing type information and flags.
    In addition, extra universal or existential quantifiers can be specified in
    a list called extras. Copies of these will also be made into the quantifier
    zone if they are encountered in the tree.
    """
    tldict = deepcopy(tl.vars) if temp else tl.vars
    vars_dict = dict()
    copied = []
    
    def process(tree, constraint=False):
        if tree == None:
            return
        if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            name = tree.var.name()
            new_name = relabel_varname(name, tldict)
            vars_dict[name] = new_name
            process(tree.var, constraint)
            process(tree.left, constraint)
        elif isinstance(tree, VarNode):
            process(tree.constraint, True)
            name = tree.name()
            if name in vars_dict:
                new_name = vars_dict[name]
                tree._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name, copied, assign)
            elif not constraint and tree.is_metavar:
                new_name = relabel_varname(name, tldict)
                vars_dict[name] = new_name
                tree._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name, copied, assign)
        elif isinstance(tree, SetBuilderNode):
            name = tree.left.left.name()
            new_name = relabel_varname(name, tldict)
            vars_dict[name] = new_name
            process(tree.left, constraint)
            process(tree.right, constraint)
        elif isinstance(tree, LRNode):
            process(tree.left, constraint)
            process(tree.right, constraint)
        elif isinstance(tree, FnApplNode):
            name = tree.name()
            if isinstance(tree.var, VarNode) and name in vars_dict:
                new_name = vars_dict[name] # TODO : add setter for assignment
                tree.var._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name, copied, assign)
            elif tree.is_metavar:
                new_name = relabel_varname(name, tldict)
                vars_dict[name] = new_name
                tree.var._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name, copied, assign)
            else:
                process(tree.var, constraint)
            for v in tree.args:
                process(v, constraint)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                process(v, constraint)
        elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset':
            process(tree.constraint, True)
        elif isinstance(tree, SetSort):
            process(tree.sort, constraint)
        elif isinstance(tree, TupleSort):
            for v in tree.sorts:
                process(v, constraint)
        elif isinstance(tree, FunctionConstraint):
            process(tree.domain, constraint)
            process(tree.codomain, constraint)
        elif isinstance(tree, CartesianConstraint):
            for v in tree.sorts:
                process(v, constraint)
        elif isinstance(tree, DomainTuple):
            for v in tree.sets:
                process(v, constraint)
            for v in tree.sort.sets:
                process(v, constraint)
    t = tree
    while isinstance(t, ForallNode) or isinstance(t, ExistsNode):
        name = t.var.name()
        new_name = relabel_varname(name, tldict)
        vars_dict[name] = new_name
        t.var._name = new_name # TODO : allow assignment of name for FnApplNode
        process(t.var.constraint)
        t = t.left

    process(t)
    return tree, copied

def append_quantifiers(tlist0, tree):
    """
    Given a tree of quantifiers that should be moved into the quantifier zone,
    append tree to the end of the existing quantifier zone (which will be index
    0 of tlist0).
    """
    if tlist0:
        qz = tlist0[0]
        while qz.left:
           qz = qz.left
        qz.left = tree
    else: # tlist0 is currently empty
        tlist0[0] = tree

def append_tree(tlist, stmt, dirty):
    """
    Append the given statement to the given tree list. This is used to add a
    hypothesis or target. The function is supplied with a list, dirty, of all
    the line numbers of the tableau that must be updated. We append the
    relevant line number to this list.
    """
    n = len(tlist)
    tlist.append(stmt)
    if dirty != None and n not in dirty:
        dirty.append(n)

def replace_tree(tlist, i, stmt, dirty):
    """
    Replace the i-th element of the given tree list with the given statement.
    This is used when replacing a hypothesis or target with one derived from
    it. The function is supplied with a list, dirty, of all the line numbers
    of the tableau that must be updated. We append the relevant line number to
    this list.
    """
    tlist[i] = stmt
    if dirty != None and i not in dirty:
        dirty.append(i)

def append_tree2(pad, tlist, stmt):
    """
    As per append_tree, but the relevant line of the given pad is also updated.
    """
    n = len(tlist)
    append_tree(tlist, stmt, None)
    pad[n] = str(tlist[n])

def replace_tree2(pad, tlist, i, stmt):
    """
    As per replace_tree, but the relevant line of the given pad is also
    updated.
    """
    replace_tree(tlist, i, stmt, None)
    pad[i] = str(tlist[i])

def record_move(screen, tl, i, reason):
    moves = tl.moves
    num = len(moves)
    if i >= num:
        for j in range(num, i + 1):
            moves.append([])
    moves[i].append(reason)

def duplicate_move(screen, tl, i, k):
    moves = tl.moves
    num = len(moves)
    if i >= num:
        for j in range(num, i + 1):
            moves.append([])
    moves[i] = moves[k]

def prune_move_list(screen, tl, ttree):
    moves = tl.moves
    tars = [] # list of targets required by proof
    hyps = [] # list of hypotheses required by proof
    unproc = [] # unprocessed list
    if not ttree:
        return [], []
    for node in ttree.andlist:
        unproc.append(node)
    while unproc: # process targets
        node = unproc.pop()
        tars.append(node.num)
        for i in node.extra_hyps:
            if i not in hyps:
                hyps.append(i)
        if node.reason == None: # proved by proving targets in andlist
            for n in node.andlist:
                unproc.append(n)
        elif isinstance(node.reason, tuple):
            (i, j) = node.reason
            if i not in hyps:
                hyps.append(i)
            if j not in hyps:
                hyps.append(j)
        elif node.reason != -1:
            i = node.reason
            if i not in hyps:
                hyps.append(i)
    unproc = hyps
    hyps = []
    while unproc: # process hyps
        i = unproc.pop()
        if i not in hyps:
            hyps.append(i)
            if i < len(moves):
                reason = moves[i] # list of moves applied to prove i
                for r in reason:
                    if len(r) == 3: # mp/mt/equiv
                        (c, l1, l2_list) = r
                        unproc.append(l1)
                        unproc += l2_list
                    else: # cleanup
                        c, l = r
                        unproc.append(l)
    return sorted(hyps), sorted(tars)
            
def treelist_prune(screen, tl, new_tl, hyps, tars):
    """
    Given a list of hypotheses and targets to keep and a new tableau, place
    only the given items in the new tableau.
    """
    tlist0 = tl.tlist0.data
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    var_list = []
    for i in range(len(hyps)):
        new_tl.tlist1.data.append(tlist1[hyps[i]])
    for i in range(len(tars)):
        new_tl.tlist2.data.append(tlist2[tars[i]])
    for tree in new_tl.tlist1.data:
        v = vars_used(screen, tl, tree, True)
        var_list = list_merge(var_list, sorted(v))
    for tree in new_tl.tlist2.data:
        v = vars_used(screen, tl, tree, True)
        var_list = list_merge(var_list, sorted(v))
    if tlist0:
        qz = NotNode(tlist0[0]) # temporary wrapper
        tree = qz
        while tree.left:
            if tree.left.var.name() not in var_list:
                tree.left = tree.left.left
            else:
                tree = tree.left
        if qz.left:
            new_tl.tlist0.data.append(qz.left)
    new_tl.focus = new_tl.tlist1
    
def is_implication(tree):
    """
    Given a parse tree, determine whether it is an implication, possibly
    quantified.
    """
    if isinstance(tree, ForallNode):
        return is_implication(tree.left)
    return isinstance(tree, ImpliesNode)

def is_equality(tree):
    """
    Given a parse tree, determine whether it is an equality, possibly
    quantified.
    """
    if isinstance(tree, ForallNode):
        return is_equality(tree.left)
    return isinstance(tree, EqNode)
    
def metavars_used(tree):
    """
    Given a parsed statement, return a list of names of metavariables (as
    strings) that occur in the given statement.
    """
    used = []

    def search(tree):
        if tree == None:
            return
        elif isinstance(tree, SetOfNode):
            pass
        elif isinstance(tree, LRNode):
            search(tree.left)
            search(tree.right)
        elif isinstance(tree, VarNode):
            if tree.is_metavar:
                name = tree.name()
                if name not in used:
                    used.append(name)
        elif isinstance(tree, FnApplNode):
            if tree.is_metavar:
                name = tree.name()
                if name not in used:
                    used.append(name)
            for v in tree.args:
                search(v)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                search(v)
        
    search(tree)
    return used

def is_duplicate_upto_metavars(tree1, tree2, sk=None, from_vars=None, to_vars=None):
    """
    Return True if the two parse trees are the same with the possible exception
    of metavariables with different names.
    """
    mv_dict = dict() # corresponding name in tree2 of metavars found in tree1
    new_from = [] # variables renamed to
    new_to = [] # variables renamed to

    def process(tree1, tree2, mv_dict):
        if tree1 == None:
            return tree2 == None
        if tree2 == None:
            return False
        if type(tree1) != type(tree2):
            return False
        if isinstance(tree1, DeadNode):
            return True
        if isinstance(tree1, VarNode):
            if tree1.is_metavar != tree2.is_metavar:
                return False
            if tree1.name() in mv_dict:
                return tree2.name() == mv_dict[tree1.name()]
            elif tree1.is_metavar:
                mv_dict[tree1.name()] = tree2.name()
                if sk:
                    new_from.append(tree1.name())
                    new_to.append(tree2.name())
                return True
            else:
                return tree1.name() == tree2.name()
        elif isinstance(tree1, FnApplNode):
            if sk:
                if tree1.is_skolem:
                    if not tree2.is_skolem:
                        return False
                    name1 = tree1.name()
                    name2 = tree2.name()
                    if name2 in sk:
                        found = False
                        for i in range(len(from_vars)):
                            if name1 == from_vars[i]:
                                found = True
                                if name2 != to_vars[i]:
                                    return False
                                break
                        if not found:
                            for i in range(len(new_from)):
                                if name1 == new_from[i]:
                                    found = True
                                    if name2 != new_to[i]:
                                        return False
                                    break
                        if not found:
                            new_from.append(name1)
                            new_to.append(name2)
            if not process(tree1.var, tree2.var, mv_dict):
                return False
            if len(tree1.args) != len(tree2.args):
                return False
            for i in range(len(tree1.args)):
                if not process(tree1.args[i], tree2.args[i], mv_dict):
                    return False
            return True
        elif isinstance(tree1, TupleNode):
            if len(tree1.args) != len(tree2.args):
                return False
            for i in range(len(tree1.args)):
                if not process(tree1.args[i], tree2.args[i], mv_dict):
                    return False
            return True
        elif isinstance(tree1, LRNode):
            if not process(tree1.left, tree2.left, mv_dict):
                return False
            return process(tree1.right, tree2.right, mv_dict)
        elif isinstance(tree1, SymbolNode):
            return tree1.name() == tree2.name()
        elif isinstance(tree1, NaturalNode) or isinstance(tree1, BoolNode):
            return tree1.value == tree2.value
        elif isinstance(tree1, Universum):
            return isinstance(tree2, Universum)
        elif isinstance(tree1, SetSort):
            return process(tree1.sort, tree2.sort, mv_dict)
        elif isinstance(tree1, NumberSort):
            return tree1.name() == tree2.name()
        elif isinstance(tree1, TupleSort):
            if len(tree1.sorts) != len(tree2.sorts):
                return False
            for i in range(len(tree1.sorts)):
                if not process(tree1.sorts[i], tree2.sorts[i], mv_dict):
                    return False
            return True
        else:
            raise Exception("Type "+str(type(tree1))+" unknown")

    val = process(tree1, tree2, mv_dict)
    if sk and val:
        for i in new_from:
            from_vars.append(i)
        for i in new_to:
            to_vars.append(i)
    return val

class TargetNode:
    """
    Used for building a tree of targets so we can keep track of which targets
    when proved will constitute a proof of which other targets. For this
    purpose, the target with number num has an andlist which is a list of
    target nodes of all the targets that have to be proved in order to prove
    it.
    """
    def __init__(self, num, andlist=[]):
        self.num = num # which target this node corresponds to
        self.proved = False # start in unproved state
        self.andlist = andlist # a list of targets that would prove this target
        self.metavars = [] # metavariables used by this target
        self.unifies = [] # list of hyps this target unifies with on its own
        self.reason = None # how target was proved (hyp. i, contr. (i, j), equal. -1, andlist None)
        self.extra_hyps = [] # any extra hypotheses which were needed to prove node

    def __str__(self):
        if not self.andlist:
            return "("+str(self.num)+")"
        else:
            return "("+str(self.num)+", ["+", ".join([str(j) for j in self.andlist])+"])"

def target_metavars(screen, tl, ttree):
    """
    Return a sorted list of the names of all metavariables used in all targets
    in the given target tree (which may be a subtree of the whole target tree).
    """
    target_metavars = []
    tlist2 = tl.tlist2.data
    
    def mvars(ttree, target_metavars):
        if ttree.proved:
            return target_metavars
        if ttree.num != -1:
            ttree.metavars = metavars_used(tlist2[ttree.num])
            ttree.metavars.sort()
            target_metavars = list_merge(target_metavars, ttree.metavars)
        for t in ttree.andlist:
            target_metavars = mvars(t, target_metavars)
        return target_metavars

    return mvars(ttree, target_metavars)

def add_sibling(screen, tl, ttree, i, j):
    """
    Find target i in the given target tree and add a sibling j for it. This is
    done when a target is replaced with multiple targets, e.g. when we split a
    conjunction. Each of the new targets j then has to be proved along with
    target i to close out that branch, so they are added using this function to
    the same andlist that i appeared in.
    """
    for P in ttree.andlist:
        if P.num == i:
            jnode = TargetNode(j)
            ttree.andlist.append(jnode)
            for k in range(len(tl.tlist1.data)): # hyps that prove i also prove j
                if k in tl.tlist1.dep:
                     if i in tl.tlist1.dep[k]: # add j to list
                          tl.tlist1.dep[k].append(j)
            return True
    for P in ttree.andlist:
        if add_sibling(screen, tl, P, i, j):
            return True
    return False

def add_descendant(ttree, i, j, hyp=None):
    """
    Find target i in the given target tree and add a descendent j. This is
    done when proving target j will be sufficient to prove target i, e.g.
    because we reasoned backwards to j from i.
    """
    if ttree.num == i:
        n = TargetNode(j)
        if hyp:
            n.extra_hyps.append(hyp)
        ttree.andlist = [n]
        return True
    for P in ttree.andlist:
        if add_descendant(P, i, j, hyp):
            return True
    return False

def metavar_check(screen, tree1, tree2):
    """
    Check if the two trees have metavariables in common.
    """
    var1 = metavars_used(tree1)
    var2 = metavars_used(tree2)
    return not any(t in var1 for t in var2)
    
def deps_compatible(screen, tl, ttree, i, j):
    """
    Return True if hypothesis j can be used to prove target i. Otherwise,
    return False.

    Note that -1 in a target dependency list specifies that the hypothesis in
    question can be used in the proof of any target.

    The function takes a target dependency tree (ttree) which specifies
    how the targets relate to one another.
    """
    dep_list = tl.tlist1.dependency(j) # targets provable by hypothesis j
    if -1 in dep_list: # hyp j can prove anything
        return True

    def find(ttree, i):
        if ttree.num == i:
            return ttree
        for P in ttree.andlist:
            t = find(P, i)
            if t:
                return t
        return None

    for d in dep_list:
        root = find(ttree, d) # find target d
        if find(root, i): # target i is a descendant of d
            return True
    return False

def deps_intersect(screen, tl, ttree, i, j):
    """
    Return a list of targets which hypotheses i and j may both be used to
    prove. Not all targets are listed, but just targets corresponding to roots
    of subtrees in the target dependency tree which are sufficient to mark the
    nodes below which everything can be proved by hypotheses i and j.

    Note that -1 in a target dependency list specifies that the hypothesis in
    question can be used in the proof of any target.

    The function takes a target dependency tree (ttree) which specifies how
    the targets relate to one another.
    """
    deps_i = tl.tlist1.dependency(i) # targets provable by hyp i
    deps_j = tl.tlist1.dependency(j) # targets provable by hyp j
    if -1 in deps_i:
         return deps_j
    if -1 in deps_j:
         return deps_i
    deps = []
    for d1 in deps_j:
        for d2 in deps_i:
            if d1 < d2:
                d1, d2 = d2, d1
            if target_depends(screen, tl, ttree, d1, d2):
                if d1 not in deps:
                    deps.append(d1)
    return deps

def deps_defunct(screen, tl, ttree, i, j):
    """
    Return True if proving target i would make hypothesis j defunct on the
    grounds that it could only be used to prove i or one of its dependencies.

    Note that -1 in a target dependency list specifies that the hypothesis in
    question can be used in the proof of any target.
    
    The function takes a target dependency tree (ttree) which specifies how
    the targets relate to one another.
    """
    deps_j = tl.tlist1.dependency(j) # targets provable by hyp j
    if -1 in deps_j: # hyp j can prove everything, can't be made defunct
        return False

    def find(ttree, i):
        if ttree.num == i:
            return ttree
        for P in ttree.andlist:
            t = find(P, i)
            if t:
                return t
        return None

    root = find(ttree, i)
    for d in deps_j:
        if not find(root, d): # we can't prove d from i
            return False
    return True

def target_depends(screen, tl, ttree, i, j):
     """
     Return True if target i is a descendant of j, i.e. if target i were
     proved, target j would no longer be useful as it only existed as part
     of some backwards reasoned sufficient condition(s) for proving i.

    The function takes a target dependency tree (ttree) which specifies how
    the targets relate to one another.
     """
     def find(ttree, i):
        if ttree.num == i:
            return ttree
        for P in ttree.andlist:
            t = find(P, i)
            if t:
                return t
        return None

     root = find(ttree, j) # find target j
     if find(root, i): # i is a descendant of j
         return True
     return False

def target_compatible(screen, tl, ttree, dep_list, j, forward):
    """
    If forward=True, this function returns the "intersection" of the list
    of targets specified in dep_list and the list of targets which hypothesis
    j may be used to prove.

    "Intersection" here takes into account that the lists won't necessarily
    include all targets, but merely a set of targets which correspond to roots
    of subtrees in the target dependency graph. The list returned has the same
    property.

    The computation is involved because it may be that one such target is
    further down the tree than one in the list that is being intersected, and
    the "intersection" needs to only include the one further down the tree.

    If forward=False, this function returns dep_list if the *target* j is
    amongst those that can be proved from the targets listed in dep_list.
    Otherwise it returns None.

    Note that -1 in a target dependency list specifies that the hypothesis in
    question can be used in the proof of any target.
    """
    if forward: # return "intersection" of lists
        deps_j = tl.tlist1.dependency(j) # targets provable from j
        if -1 in deps_j:
            return dep_list
        if -1 in dep_list:
            return deps_j
        deps = []
        for d1 in deps_j:
            for d2 in dep_list:
               if d1 < d2:
                   d1, d2 = d2, d1
               if target_depends(screen, tl, ttree, d1, d2):
                   if d1 not in deps:
                       deps.append(d1)
        return deps
    else: # return original list or [] depending if target j is target compatible
        if -1 in dep_list:
            return dep_list
        for d in dep_list:
            if target_depends(screen, tl, ttree, j, d):
                return dep_list
        return None

class SortNode:
    def __init__(self, sort):
        self.sort = sort
        self.follow = True # whether this node really follows from its ancestor (for powersets)
        self.subsorts = []

def initialise_sorts(screen, tl):
    """
    Initialise the internally maintained sort graph. At the top is the sort
    \mathcal{U} and we add all the number types to this sort graph with the
    obvious inclusions.
    """
    tl.stree = [SortNode(Universum())]
    C = NumberSort("\\mathbb{C}", CompleteValuedFieldClass())
    R = NumberSort("\\mathbb{R}", CompleteOrderedValuedFieldClass())
    Q = NumberSort("\\mathbb{Q}", FieldClass())
    Z = NumberSort("\\mathbb{Z}", OrderedRingClass())
    N = NumberSort("\\mathbb{N}", OrderedSemiringClass())
    insert_sort(screen, tl, Universum(), C)
    insert_sort(screen, tl, C, R)
    insert_sort(screen, tl, R, Q)
    insert_sort(screen, tl, Q, Z)
    insert_sort(screen, tl, Z, N)   

def find_sort(screen, tl, s):
    """
    Given the tree of sorts, stree, find the sort s (as a node) in the tree.
    If it is not found, return False. TupleSorts are added if their components
    are in the tree and they are not found.
    """
    stree = tl.stree

    if isinstance(s, SetSort): # for powersets
        r = find_sort(screen, tl, s.sort)
        if not r:
            return None
        for t in r.subsorts:
            if sorts_equal(s, t.sort):
                return t
        # not found, so add it with a nofollow
        t = SortNode(s)
        t.follow = False # this is a powerset and is not actually a descendent of r
        r.subsorts.append(t)
        return t
    if isinstance(s, TupleSort):
        for r in s.sorts:
            if not find_sort(screen, tl, r):
                return None
        n = len(s.sorts)
        if n > len(stree): # types of correct arity don't exist yet
            for i in range(len(stree), n):
                t = TupleSort([Universum() for j in range(i)])
                stree.append(SortNode(t))
        else:
            for t in stree[n - 1].subsorts:
                if sorts_equal(s, t.sort):
                    return t
        t = SortNode(deepcopy(s))
        stree[n - 1].subsorts.append(t)
        if tl.sorts_recording: # if we are recording modifications in case of rollback
            tl.sorts_record.append(stree[n-1].subsorts)
        return t
    else:
        def find(st, s):
            for t in st.subsorts:
                if sorts_equal(s, t.sort):
                    return t
                r = find(t, s)
                if r:
                    return r
            return None
        
        for i in range(len(stree)):
            if sorts_equal(s, stree[0].sort):
                return stree[0]

            r = find(stree[0], s)
            if r:
                return r
        return None

def sort_descendant(screen, tl, s1, s2):
    """
    Given a base node s1 in the stree, find s2 starting at that node.
    Otherwise return None.
    """
    if sorts_equal(s1.sort, s2):
        return s1
    for t in s1.subsorts:
        if t.follow: # check t is actually reachable
            r = sort_descendant(screen, tl, t, s2)
            if r:
                return r
    return None

def insert_sort(screen, tl, s1, s2):
    """
    Make s2 a subsort of s1 by adding it to the internally maintained sort
    tree in the appropriate location. It is assumed that the sort s1 already
    exists in the tree.
    """
    r = find_sort(screen, tl, s1)
    r.subsorts.append(SortNode(s2))
    if tl.sorts_recording: # if we are recording modifications in case of rollback
        tl.sorts_record.append(r.subsorts)

def sorts_mark(screen, tl):
    tl.sorts_recording = True
    tl.sorts_record = []

def sorts_rollback(screen, tl):
    while tl.sorts_record:
        s = tl.sorts_record.pop()
        s.pop()
    tl.sorts_recording = False

def sorts_equal(s1, s2, assign=None):
    """
    Return True if two sorts are equal, else return False.
    """
    if type(s1) != type(s2):
        return False
    if isinstance(s1, VarNode) and s1.is_metavar:
        if assign != None:
            assign.append((s1, s2))
        return True
    if isinstance(s2, VarNode) and s2.is_metavar:
        if assign != None:
            assign.append((s2, s1))
        return True
    elif isinstance(s1, VarNode) or isinstance(s1, NumberSort):
        return s1.name() == s2.name()
    elif isinstance(s1, SetSort):
        return sorts_equal(s1.sort, s2.sort)
    elif isinstance(s1, TupleSort):
        if len(s1.sorts) != len(s2.sorts):
            return False
        for i in range(len(s1.sorts)):
            if not sorts_equal(s1.sorts[i], s2.sorts[i]):
                return False
        return True
    elif isinstance(s1, PredSort) or isinstance(s1, Universum):
        return True
    return False

def coerce_sorts(screen, tl, s1, s2, assign=None):
    # special case, used only by sorts_compatible for function domains
    if s1 == None and s2 == None:
        return True
    if isinstance(s1, VarNode) and s1.is_metavar:
        if assign != None:
            assign.append((s1, s2))
        return s2
    if isinstance(s2, VarNode) and s2.is_metavar:
        if assign != None:
            assign.append((s2, s1))
        return s1
    if isinstance(s1, TupleSort) and isinstance(s2, TupleSort):
       if len(s1.sorts) != len(s2.sorts):
           return None
       sorts = [coerce_sorts(screen, tl, s1.sorts[i], s2.sorts[i], assign) for i in range(len(s1.sorts))]
       if None in sorts:
           return None
       return TupleSort(sorts)
    if isinstance(s1, SetSort) and isinstance(s2, SetSort):
       return coerce_sorts(screen, tl, s1.sort, s2.sort, assign)
    # if s2 can be coerced to s1, return s1, else None
    if sorts_equal(s1, s2, assign):
        return s1
    b = find_sort(screen, tl, s1)
    if b:
        return sort_descendant(screen, tl, b, s2)
    return None # not coercible
    
def sorts_compatible(screen, tl, s1, s2, assign=None, both_dirs=True):
    if isinstance(s1, SetOfNode) and isinstance(s2, SetOfNode):
        return sorts_compatible(s1.left), sorts_compatible(s2.left)
    if isinstance(s1, SetOfNode) or isinstance(s2, SetOfNode):
        return False
    if isinstance(s1, Universum) and isinstance(s2, Universum):
        return True
    if isinstance(s1, VarNode) and s1.is_metavar:
        if assign != None:
            assign.append((s1, s2))
        return True
    if isinstance(s2, VarNode) and s2.is_metavar:
        if assign != None:
            assign.append((s2, s1))
        return True
    t1 = isinstance(s1, TupleSort)
    t2 = isinstance(s2, TupleSort)
    if (t1 and not t2) or (t2 and not t1):
        return False
    if t1:
        if len(s1.sorts) != len(s2.sorts):
            return False 
        compatible = True
        for i in range(len(s1.sorts)):
            # TODO : check assignments are compatible
            if not coerce_sorts(screen, tl, s1.sorts[i], s2.sorts[i], assign):
                compatible = False
                break
        if not compatible:
            compatible = True
            for i in range(len(s1.sorts)):
                # TODO : check assignments are compatible
                if not coerce_sorts(screen, tl, s2.sorts[i], s1.sorts[i], assign):
                    compatible = False
                    break
        return compatible
    c1 = isinstance(s1, SetSort)
    c2 = isinstance(s2, SetSort)
    if (c1 and not c2) or (c2 and not c1):
         return False 
    if c1:
         return sorts_compatible(screen, tl, s1.sort, s2.sort, assign, both_dirs)
    if coerce_sorts(screen, tl, s1, s2, assign):
        return True
    if coerce_sorts(screen, tl, s2, s1, assign):
        return True
    return False

def sort_type_class(sort):
    """
    Return the typeclass that a given sort belongs to.
    """
    if isinstance(sort, VarNode):
        return sort.constraint.typeclass
    elif isinstance(sort, NumberSort) or isinstance(sort, Universum):
        return sort.typeclass
    else:
        raise Exception("Not a valid sort")

# abbreviations for number types
canonical_numconstraints = { "\\N" : "\\mathbb{N}",
                       "\\Z" : "\\mathbb{Z}",
                       "\\Q" : "\\mathbb{Q}",
                       "\\R" : "\\mathbb{R}",
                       "\\C" : "\\mathbb{C}"}

def tags_to_list(tags):
    """
    Given a string of space separated hashtags, create a list of strings with
    the individual tags as elements. The list may be empty.
    No processing is done to check the tags are valid, or even that they are
    hashtags.
    """
    t = tags[6:].split(" ")
    if len(t) == 1 and t[0] == '':
        t = []
    return t

def canonicalise_tags(tags):
    """
    Given a string of space separate hashtags, return the same string with
    'Tags: ' prepended and with any number types canonicalised, i.e. such that
    any abbreviations are replaced with their full latex.
    No processing is done to check that the tags are valid, or even that they
    are hashtags.
    """
    taglist = tags_to_list(tags)
    for i in range(0, len(taglist)):
        tag = taglist[i][1:]
        if tag in canonical_numconstraints:
            taglist[i] = "#"+canonical_numconstraints[tag]
    return "Tags: "+' '.join(taglist)

def filter_titles(titles, c):
    """
    Given a list of pairs consisting of a string representing a theorem title
    and an integer (representing a position within the library file) and a
    character c, return a similar list of pairs consisting of just those for
    which the first letter of the title is the given character (or the upper
    case version of it).
    """
    titles2 = []
    for (line, v) in titles:
        if v[0] == c or v[0] == c.upper():
            titles2.append((line, v))
    return titles2

def trim_spaces(string, start, end):
    """
    Given a string and a range [start, end) delineating a substring, return a
    pair consisting of a new start position and the substring of the original
    substring with any spaces trimmed off each end.
    """
    while start <= end and string[start] == ' ':
        start += 1
    while end > start and string[end - 1] == ' ':
        end -= 1
    return start, string[start:end]

def find_all(string, substring):
    """
    Return a list of all indices of the given substring in the given string.
    Instances are excluded if they overlap.
    """
    start = 0
    res = []
    n = len(substring)
    while True:
        start = string.find(substring, start)
        if start == -1:
            return res
        res.append(start)
        start += n

def find_start_index(lst, chosen_set):
    """
    Given a list lst of items, find the index of the first element of the list
    such that no element from that point on (inclusive) is in the list of items
    denoted chosen_set.
    """
    index = len(lst)
    for i in reversed(range(len(lst))):
        if lst[i] in chosen_set:
            break
        index = i
    return index

def list_merge(list1, list2):
    """
    Given two lists, merge the two lists together, eliminating duplicates from
    the merge. Return the resulting merged list. Both lists are assumed to be
    sorted and the standard comparison function is used to ensure the result
    remains sorted.
    """
    if list1 == []:
        return list2
    if list2 == []:
        return list1
    r = []
    L = merge(list1, list2)
    v = ''
    for var in L:
        if var != v:
           r.append(var)
        v = var
    return r

def merge_lists(lol):
    """
    Given a list of lists, merge the lists together into a single list.
    """
    if len(lol) == 0:
        return []
    elif len(lol) == 1:
        return lol[0]
    else:
        L = lol[0]
        for i in range(1, len(lol)):
            L = list_merge(L, lol[i])
        return L

def get_constraint(var, qz):
    """
    Given a variable var and the quantifier zone qz, find the constraint for
    the variable in qz and return it. This function raises an exception if
    the variable doesn't exist in qz.
    """
    tree = qz
    name = var.name()
    while qz:
        if qz.var.name() == name:
            return qz.var.constraint
        qz = qz.left
    raise Exception("Binder not found for "+var.name())

constant_dict = {
        ExpNode : '^',
        CircNode : '\\circ',
        TupleComponentNode : '[]',
        PowerSetNode : '\\mathcal{P}',
        AddNode : '+',
        SubNode : '-',
        MulNode : '*',
        DivNode : '/',
        LtNode : '<',
        GtNode : '>',
        LeqNode : '\\leq',
        GeqNode : '\\geq',
        EqNode : '=',
        NeqNode : '\\neq',
        IffNode : '\\iff',
        ImpliesNode : '\\implies',
        CartesianNode : '\\times',
        IntersectNode : '\\cap',
        UnionNode : '\\cup',
        SubsetneqNode : '\\subsetneq',
        SubseteqNode : '\\subseteq',
        SupsetneqNode : '\\supsetneq',
        SupseteqNode : '\\supseteq',
        DiffNode : '\\setminus',
        SetBuilderNode : '{|}',
        AbsNode : '||',
        NegNode : '-',
        ElemNode : '\\in',
        BoolNode : 'T/F',
        CartesianConstraint : '\\times',
        FunctionConstraint : '->',
        SetSort : 'Set',
        PredSort : 'Pred'   
    }

def append_unique(list, item):
    """
    Given a list, if the given item is not in the list, append it.
    """
    if item not in list:
        list.append(item)

def get_constants_qz(screen, tl, tree):
    constants = []

    while tree:
        constants = get_constants(screen, tl, tree.var.constraint, constants)
        tree = tree.left

    constants.sort()
    return constants

def get_constants(screen, tl, tree, constants_in=[]):
    """
    Given a parse tree, return a list of all constants used in the statement,
    i.e. excluding all variable names but including function names which are
    meaningful to the system. Each name appears once and the list will be
    sorted.
    """
    constants = deepcopy(constants_in)
    
    def process(tree):
        if tree == None:
            return
        if isinstance(tree, SymbolNode):
            append_unique(constants, tree.name())
        elif isinstance(tree, VarNode) or isinstance(tree, SetOfNode) \
          or isinstance(tree, DeadNode) or isinstance(tree, LambdaNode) \
          or isinstance(tree, ForallNode) or isinstance(tree, ExistsNode) \
          or isinstance(tree, Universum) or isinstance(tree, AndNode) \
          or isinstance(tree, OrNode) or isinstance(tree, NotNode)  \
          or isinstance(tree, SetSort):
            pass
        elif isinstance(tree, FnApplNode):
            if isinstance(tree.var, VarNode):
                name = tree.var.name()
                if (name in system_unary_functions and name != 'universe') or \
                   (name in system_binary_functions) or \
                   (name in system_predicates):
                    append_unique(constants, name)
        elif isinstance(tree, TupleNode):
            append_unique(constants, 'Tuple('+str(len(tree.args))+')')
        elif isinstance(tree, NaturalNode):
            append_unique(constants, str(tree.value))
        elif isinstance(tree, NumberSort):
            append_unique(constants, tree.name())
        elif isinstance(tree, TupleSort):
            append_unique(constants, 'Tuple('+str(len(tree.sorts))+')')
        elif isinstance(tree, BoolNode):
            if tree.value:
                append_unique(constants, "True")
            else:
                append_unique(constants, "False")
        else:
            append_unique(constants, constant_dict[type(tree)])
        
        if isinstance(tree, LRNode):
            process(tree.left)
            process(tree.right)
        if isinstance(tree, TupleNode) or isinstance(tree, FnApplNode):
            for v in tree.args:
                process(v)
        if isinstance(tree, FnApplNode):
            process(tree.var) # for composite functions
        if isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
            process(tree.var.constraint)
        if isinstance(tree, CartesianConstraint) or isinstance(tree, TupleSort):
            for v in tree.sorts:
                process(v)
        if isinstance(tree, FunctionConstraint):
            process(tree.domain)
            process(tree.codomain)
        if isinstance(tree, DomainTuple):
            for v in tree.sets:
                process(v)
        if isinstance(tree, SetSort):
            process(tree.sort)
        
    process(tree)
    constants.sort()
    return constants

def get_init_vars(screen, tl, qz):
    """
    Given a quantifier zone for a theorem, make a list of all the names of the
    initial variables, i.e. universally quantified variables present in the
    initial tableau.
    """
    vars = []
    while qz:
        if isinstance(qz, ForallNode) and not qz.var.is_metavar:
            vars.append(qz.var.name())
        qz = qz.left
    return vars

def is_atom(screen, tl, tree, vars):
    """
    Returns a triple a, A, Au where a is True if the given tree is an
    atomic string consisting of a variable in vars, constant or application
    of unary functions thereto, A is the string of the variable or constant
    involved and Au is the string of the entire atomic string. 
    """
    if isinstance(tree, VarNode):
        name = tree.name()
        return (name in vars), name, name
    elif isinstance(tree, AbsNode):
        a, A, Au = is_atom(screen, tl, tree.left, vars)
        return a, A, "|"+Au+"|"
    elif isinstance(tree, NegNode):
        a, A, Au = is_atom(screen, tl, tree.left, vars)
        return a, A, "-("+Au+")"
    elif isinstance(tree, SetOfNode):
        return is_atom(screen, tl, tree.left, vars)
    elif isinstance(tree, SymbolNode):
        name = tree.name()
        return True, name, name
    elif isinstance(tree, NaturalNode):
        s = str(tree.value)
        return True, s, s
    elif isinstance(tree, TupleComponentNode):
        a, A, Au = is_atom(screen, tl, tree.left, vars)
        return a, A, Au+"["+str(tree.right.value)+"]"
    elif isinstance(tree, PowerSetNode):
        a, A, Au = is_atom(screen, tl, tree.left, vars)
        return a, A, "\\mathcal{P}("+Au+")"
    else:
        return False, None, None

def is_binary_op(screen, tl, tree):
    """
    Return True if the given parse tree is a binary operation applied to
    two terms.
    """
    return isinstance(tree, ExpNode) or isinstance(tree, CircNode) or isinstance(tree, AddNode) or \
           isinstance(tree, SubNode) or isinstance(tree, MulNode) or isinstance(tree, DivNode) or \
           isinstance(tree, CartesianNode) or isinstance(tree, IntersectNode) or \
           isinstance(tree, UnionNode)

def binary_string(tree, arglist):
    """
    Given a parse tree of a binary operation or function applied to a list
    of unary arguments or a tuple thereof, return a string representing the
    entire application or tuple, cleaned up for automation purposes.
    """
    if isinstance(tree, FnApplNode):
        return str(tree.var)+"("+", ".join(arglist)+")"
    elif isinstance(tree, TupleNode):
        return "("+", ".join(arglist)+")"
    else:
        return arglist[0]+" "+constant_dict[type(tree)]+" "+arglist[1]
        
def vars_used(screen, tl, tree, include_metavars=False):
    """
    Return a list of all the variables, which appear in the tree. By default
    this will not include metavars. But this can be overridden.
    """
    var_list = []
    mv = []

    def process(tree):
        if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            mv.append(tree.var.name())
            process(tree.left)
        elif isinstance(tree, VarNode):
            name = tree.name()
            if (include_metavars or not tree.is_metavar) and name not in mv:
                var_list.append(name)
        elif isinstance(tree, FnApplNode):
            if isinstance(tree.var, VarNode):
                process(tree.var)
            for v in tree.args:
                process(v)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                process(v)
        elif isinstance(tree, LRNode):
            process(tree.left)
            process(tree.right)

    process(tree)
    return var_list

def type_depth(screen, tl, tree):
    """
    Given a type of a term, determine the maximum depth of the type as measured
    by powerset depth.
    """
    if tree == None or isinstance(tree, NumberSort) or isinstance(tree, Universum) or \
        isinstance(tree, PredSort):
        return 0
    elif isinstance(tree, VarNode):
        return type_depth(screen, tl, tree.constraint.sort)
    elif isinstance(tree, TupleSort):
        return max(type_depth(screen, tl, v) for v in tree.sorts)
    elif isinstance(tree, SetSort):
        return type_depth(screen, tl, tree.sort) + 1
    else:
        raise Exception("Unknown type "+str(type(tree))) 

def type_width(screen, tl, tree):
    """
    Given a type of a term, determine the maximum width of the type as measured
    by cartesian product width.
    """
    if tree == None or isinstance(tree, NumberSort) or \
         isinstance(tree, Universum) or isinstance(tree, VarNode) or \
         isinstance(tree, PredSort):
        return 1
    elif isinstance(tree, TupleSort):
       n = len(tree.sorts) # width at this level
       if n > 2 or n < 2:
           return max(max(type_width(screen, tl, v) for v in tree.sorts), n)
       else:
           t1 = isinstance(tree.sorts[0], TupleSort)
           t2 = isinstance(tree.sorts[1], TupleSort)
           if t1 and t2:
               return type_width(screen, tl, tree.sorts[0]) + \
                      type_width(screen, tl, tree.sorts[1])
           elif t1:
               return max(type_width(screen, tl, tree.sorts[1]), \
                      1 + type_width(screen, tl, tree.sorts[0]))
           elif t2:
               return max(type_width(screen, tl, tree.sorts[0]), \
                      1 + type_width(screen, tl, tree.sorts[1]))
           else:
               return max(2, max(type_width(screen, tl, tree.sorts[0]), \
                      type_width(screen, tl, tree.sorts[1])))
    elif isinstance(tree, SetSort):
        return type_width(screen, tl, tree.sort)
    else:
        raise Exception("Unknown type "+str(type(tree)))

def function_depth(screen, tl, tree):
    """
    Given a parse tree, return the maximum function application depth.
    """
    if tree == None or isinstance(tree, LeafNode):
        return 0
    elif isinstance(tree, TupleNode):
        return max(function_depth(screen, tl, v) for v in tree.args) if tree.args else 0
    elif isinstance(tree, FnApplNode):
        return max(function_depth(screen, tl, tree.var), \
               max(function_depth(screen, tl, v) for v in tree.args) + 1) if tree.args else 1
    elif isinstance(tree, LRNode):
        return max(function_depth(screen, tl, tree.left), \
                   function_depth(screen, tl, tree.right))

def max_type_size(screen, tl, tree):
    """
    Given a type annotated parse tree, return a tuple (max_depth, max_width,
    max_fn_depth) giving the maximum depth and width of any types of any terms
    occuring in the tree and the maximum function depth.
    """
    if tree == None:
        return 0, 1, 0
    elif is_binary_op(screen, tl, tree):
        return type_depth(screen, tl, tree.sort), \
               type_width(screen, tl, tree.sort), \
               function_depth(screen, tl, tree)
    elif isinstance(tree, TupleNode) or \
         isinstance(tree, VarNode) or isinstance(tree, AbsNode) or \
         isinstance(tree, NegNode):
        return type_depth(screen, tl, tree.sort), \
               type_width(screen, tl, tree.sort), \
               function_depth(screen, tl, tree)
    elif isinstance(tree, PowerSetNode):
        d, f, w = max_type_size(screen, tl, tree.left)
        return d + 1, w, f
    elif isinstance(tree, FnApplNode):
        if isinstance(tree.var, VarNode) and tree.var.name() in system_predicates:
            d, w, f = max_type_size(screen, tl, tree.args[0])
            return d, w, f + 1
        else:
            return type_depth(screen, tl, tree.sort), \
               type_width(screen, tl, tree.sort), \
               function_depth(screen, tl, tree)
    elif isinstance(tree, SetSort):
        return type_depth(screen, tl, tree), 1, 0
    elif isinstance(tree, LeafNode):
        return 0, 1, 0
    elif isinstance(tree, LRNode):
        d1, w1, f1 = max_type_size(screen, tl, tree.left)
        d2, w2, f2 = max_type_size(screen, tl, tree.right)
        return max(d1, d2), max(w1, w2), max(f1, f2)
    else:
        raise Exception("Unknown node type "+str(type(tree)))
    
def get_terms(screen, tl, tree, vars):
    """
    Given a parse tree, compute four lists. The first is the list of all
    variables and constants that appear in the tree. The second is the set
    of all unary operations applied to a variable or constant. The third is
    the set of all binary terms, e.g. A\cap B involving unary terms. The
    fourth is the set of all full terms that appear in the tree which only
    involve constants and variables. For the purposes of this function, a
    function application of a constant function to a set of variables or
    constants or a tuple of variables or constants, etc. qualifies as a
    binary term.
    """
    terms0 = []
    terms1 = []
    terms2 = []
    termsn = []

    def process1(tree, terms0, terms1, terms2):
        if is_binary_op(screen, tl, tree):
            a, A, Au = is_atom(screen, tl, tree.left, vars)
            b, B, Bu = is_atom(screen, tl, tree.right, vars)
            if a:
                if A not in terms0:
                    terms0.append(A)
                if Au not in terms1:
                    terms1.append(Au)
            if b:
                if B not in terms0:
                    terms0.append(B)
                if Bu not in terms1:
                    terms1.append(Bu)
            if a and b:
                terms2.append(binary_string(tree, [Au, Bu]))
        elif isinstance(tree, LRNode):
            process1(tree.left, terms0, terms1, terms2)
            process1(tree.right, terms0, terms1, terms2)
        elif isinstance(tree, FnApplNode) or isinstance(tree, TupleNode):
            is_binary = True
            if isinstance(tree, FnApplNode):
                if isinstance(tree.var, VarNode):
                    name = tree.var.name()
                    is_binary = (name in system_binary_functions)
                else:
                    process1(tree.var, terms0, terms1, terms2)
                    is_binary = False
            Au_list = []
            for v in tree.args:
                a, A, Au = is_atom(screen, tl, v, vars)
                if a:
                    if A not in terms0:
                        terms0.append(A)
                    if Au not in terms1:
                        terms1.append(Au)
                    Au_list.append(Au)
                else:
                    is_binary = False
            if is_binary:
                terms2.append(binary_string(tree, Au_list))
        elif isinstance(tree, LeafNode):
            a, A, Au = is_atom(screen, tl, tree, vars)
            if a:
                if A not in terms0:
                    terms0.append(A)
                if Au not in terms1:
                    terms1.append(Au)

    def processn(tree, termsn, top=False):
        if is_binary_op(screen, tl, tree):
            t1, s1 = processn(tree.left, termsn, True)
            t2, s2 = processn(tree.right, termsn, True)
            if t1 and t2:
                str12 = binary_string(tree, [s1, s2])
                if top == False:
                    termsn.append(str12)
                return True, str12
            elif t1:
                termsn.append(s1)
            elif t2:
                termsn.append(s2)
            return False, ''
        elif isinstance(tree, FnApplNode) or isinstance(tree, TupleNode):
            flag_list = []
            str_list = []
            for v in tree.args:
                t, s = processn(v, termsn, True)
                flag_list.append(t)
                str_list.append(s)
            is_term = all(flag_list)
            fn = isinstance(tree, FnApplNode)
            if fn:
                t, s = processn(tree.var, termsn, is_term)
            if fn and is_term and t:
                str1 = binary_string(tree, str_list)
                if top == False:
                   termsn.append(str1)
                return True, str1
            elif is_term:
                for str1 in str_list:
                    termsn.append(str1)
            else:
                if fn and t:
                    termsn.append(t)
                for i in range(len(flag_list)):
                    if flag_list[i]:
                        termsn.append(str_list[i])
            return False, ''
        elif isinstance(tree, VarNode):
            name = tree.name()
            if name in vars:
                if top == False:
                    termsn.append(name)
                return True, name
        elif isinstance(tree, AbsNode):
            t, s = processn(tree.left, termsn, True)
            if t:
                str1 = '|'+s+'|'
                if top == False:
                    termsn.append(str1)
                return True, str1
        elif isinstance(tree, NegNode):
            t, s = processn(tree.left, termsn, True)
            if t:
                str1 = '-('+s+')'
                if top == False:
                    termsn.append(str1)
                return True, str1
        elif isinstance(tree, SetOfNode):
            t, s = processn(tree.left, termsn, True)
            if t:
                if top == False:
                    termsn.append(s)
                return True, s
        elif isinstance(tree, SymbolNode):
            name = tree.name()
            if top == False:
                termsn.append(name)
            return True, name
        elif isinstance(tree, NaturalNode):
            str1 = str(tree.value)
            if top == False:
                termsn.append(str1)
            return True, str1
        elif isinstance(tree, TupleComponentNode):
            t, s = processn(tree.left, termsn, True)
            if t:
                str1 = s+"["+str(tree.right.value)+"]"
                if top == False:
                    termsn.append(str1)
                return True, str1
        elif isinstance(tree, PowerSetNode):
            t, s = processn(tree.left, termsn, True)
            if t:
                str1 = "\\mathcal{P}("+s+")"
                if top == False:
                    termsn.append(str1)
                return True, str1
        elif isinstance(tree, LRNode):
            processn(tree.left, termsn, False)
            processn(tree.right, termsn, False)
            return False, ''
        return False, ''
        
    process1(tree, terms0, terms1, terms2)
    processn(tree, termsn)
    return terms0, terms1, terms2, termsn

def element_universe(screen, x):
    """
    Function constraints specify a codomain rather than a universe. This
    function can be called to compute the appropriate universe for an element
    of the codomain (or indeed the domain, if required). One must be careful
    because the domain or codomain of a function may itself be expressed using
    some other constraint, e.g. a variable, function constraint, cartesian
    constraint, etc., and each case requires special handling.
    """
    if isinstance(x, VarNode):
        return x.sort.sort
    elif isinstance(x, FunctionConstraint):
        return x.sort # the type of a function constraint must be the type of a function
    elif isinstance(x, CartesianConstraint):
        return x.sort # ?? may need to take universes of components ??
    elif isinstance(x, SetOfNode):
        if isinstance(x.left, FunctionConstraint) or isinstance(x.left, CartesianConstraint):
            return x.left.sort
        else:
            return x.left
    else: # Universum, NumberSort, TupleSort are their own sorts
        return x

def propagate_sorts_qz(screen, tl, tree):

    while tree:
        ok, error = propagate_sorts(screen, tl, tree.var.constraint)
        if not ok:
            return False, error
        ok, error = propagate_sorts(screen, tl, tree.var)
        if not ok:
            return False, error
        tree = tree.left

    return True, None
    
def propagate_sorts(screen, tl, tree0):
    """
    Given a parse tree where all variables have been annotated with their
    constraints, compute all the types for every node of the tree. The code
    to propagate types up the the tree from components of the current node
    comes first, followed by code to compute the types for the current node.
    """
    stree = tl.stree

    def propagate(tree):
        if tree == None:
            return True, None
        if isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
            ok, error = propagate(tree.var.constraint)
            if not ok:
                return False, error
            ok, error = propagate(tree.var)
            if not ok:
                return False, error
        if isinstance(tree, FnApplNode) or isinstance(tree, TupleNode):
            for v in tree.args:
                ok, error = propagate(v)
                if not ok:
                    return False, error
        if isinstance(tree, FnApplNode):
            ok, error = propagate(tree.var)
            if not ok:
                return False, error
        if isinstance(tree, FunctionConstraint):
            ok, error = propagate(tree.domain)
            if not ok:
                return False, error
            ok, error = propagate(tree.codomain)
            if not ok:
                return False, error
            if tree.domain:
                tree.sort = SetSort(TupleSort([element_universe(screen, tree.domain), element_universe(screen, tree.codomain)]))
            else:
                tree.sort = SetSort(TupleSort([None, element_universe(screen, tree.codomain)]))
        if isinstance(tree, CartesianConstraint):
            for v in tree.sorts:
                ok, error = propagate(v)
                if not ok:
                    return False, error
            tree.sort = TupleSort(tree.sorts) ##########
        if isinstance(tree, LRNode):
            ok, error = propagate(tree.left)
            if not ok:
                return False, error
            ok, error = propagate(tree.right)
            if not ok:
                return False, error
        if isinstance(tree, SetOfNode):
            tree.sort = SetSort(tree.left)
        if isinstance(tree, SymbolNode):
            ok, error = propagate(tree.constraint)
            if not ok:
                return False, error
            if tree.name() == "\\emptyset":
                 if isinstance(tree.constraint, VarNode) or isinstance(tree.constraint, SetSort):
                     tree.sort = SetSort(tree.constraint)
                 elif isinstance(tree.constraint, SetOfNode):
                     tree.sort = tree.constraint.sort
                 else:
                     tree.sort = SetSort(tree.constraint.sort)
        elif isinstance(tree, VarNode):
            if isinstance(tree.constraint, SetSort): # this variable is a set
                insert_sort(screen, tl, tree.constraint.sort, tree) # this set is a sort
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, PredSort): # this variable is a pred
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, FnApplNode): # check it is a universe of metavar
                if tree.constraint.name() != "universe":
                    # leave sort as None
                    return False, f"Variable {tree.name()} has invalid constraint"
            elif isinstance(tree.constraint, VarNode): # check it is in a set
                if not isinstance(tree.constraint.constraint, SetSort):
                    return False, f"Variable {tree.name()} has invalid constraint"
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, Universum): # variable is in universum
                tree.sort = tree.constraint
            elif isinstance(tree.constraint, CartesianConstraint):
                ok, error = propagate(tree.constraint)
                if not ok:
                    return False, error
                tree.sort = tree.constraint.sort
            elif isinstance(tree.constraint, FunctionConstraint):
                tree.sort = tree.constraint.sort
            elif isinstance(tree.constraint, NumberSort):
                tree.sort = tree.constraint
        elif isinstance(tree, TupleComponentNode):
            lsort = tree.left.sort
            if not isinstance(lsort, TupleSort):
                return False, "Invalid tuple in component operation"
            idx = tree.right.value
            if idx < 0 or idx >= len(lsort.sorts):
                return False, "Invalid tuple index"
            tree.sort = lsort.sorts[idx] #######
        elif isinstance(tree, CartesianNode):
            if not isinstance(tree.left.sort, SetSort) or \
               not isinstance(tree.right.sort, SetSort):
                return False, "Cartesian product requires sets"
            tree.sort = SetSort(TupleSort([tree.left.sort.sort, tree.right.sort.sort]))
        elif isinstance(tree, NaturalNode):
            pass # dealt with by constructor
        elif isinstance(tree, ExpNode):
            if isinstance(tree.left.sort, Sort) and not isinstance(tree.left.sort, NumberSort):
                return False, "Cannot raise {str(tree.left)} to power"
            elif not isinstance(sort_type_class(tree.left.sort), SemiringClass):
                    return False, "Cannot raise {str(tree.left)} to power"
            if not isinstance(tree.right.sort, NumberSort) or tree.right.sort.name() != "Natural":
                    return False, "Powering operation not supported"
            tree.sort = tree.left.sort
        elif isinstance(tree, CircNode):
            lsort = tree.left.sort
            rsort = tree.right.sort
            if not is_function_type(lsort) or \
               not is_function_type(rsort):    
                return False, "Not a function in composition"
            if not sorts_equal(lsort.sort.sorts[0], rsort.sort.sorts[1]):
                return False, "Type mismatch in function composition"
            tree.sort = SetSort(TupleSort([rsort.sort.sorts[0], lsort.sort.sorts[1]]))
        elif isinstance(tree, FnApplNode):
            if tree.name() in system_unary_functions or tree.name() in system_binary_functions:
                tree.sort = tree.args[0].sort
            elif tree.name() in system_predicates:
                tree.sort = PredSort()
            elif len(tree.args) == 0: # constant function
                fn_sort = tree.var.sort
                if fn_sort.sort.sort.sorts[0] != None:
                     return False, f"Wrong number of arguments to function {tree.name()}"
                tree.sort = fn_sort.sort.sort.sorts[1]
            else:
                fn_sort = tree.var.sort
                if isinstance(fn_sort, PredSort):
                    if len(tree.args) != 1:
                        return False, f"Wrong number of arguments in predicate {tree.name()}"
                    tree.sort = PredSort()
                else:
                    domain_sort = fn_sort.sort.sort.sorts[0]
                    codomain_sort = fn_sort.sort.sort.sorts[1]
                    if domain_sort == None:
                        return False, f"Wrong number of arguments to function {tree.name()}"
                    if len(tree.args) == 1:
                        if not coerce_sorts(screen, tl, domain_sort, tree.args[0].sort):
                            return False, f"Type mismatch for argument {0} of {tree.name()}"
                    else:
                        if len(tree.args) != len(domain_sort.sorts):
                            return False, f"Wrong number of arguments to function {tree.name()}"
                        for i in range(len(tree.args)):
                            if not coerce_sorts(screen, tl, domain_sort.sorts[i], tree.args[i].sort):
                                return False, f"Type mismatch for argument {i} of {tree.name()}"
                    tree.sort = codomain_sort
        elif isinstance(tree, LambdaNode):
            # can only be created by the system
            tree.sort = SetSort(TupleSort([tree.left.sort, tree.right.sort]))
        elif isinstance(tree, TupleNode):
            # will be used for all sorts of things, so no point checking anything
            tree.sort = TupleSort([v.sort for v in tree.args])
        elif isinstance(tree, PowerSetNode):
            if not isinstance(tree.left.sort, SetSort):
                return False, "Argument to power set not a set"
            tree.sort = SetSort(tree.left.sort)
        elif isinstance(tree, AddNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                return False, "Type mismatch in addition"
            if not isinstance(sort_type_class(tree.left.sort), MonoidClass):
                return False, "Invalid type for addition"
            if not isinstance(sort_type_class(tree.right.sort), MonoidClass):
                return False, "Invalid type for addition"
            tree.sort = tree.left.sort
        elif isinstance(tree, MulNode) or isinstance(tree, SubNode) or \
             isinstance(tree, DivNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                return False, "Type mismatch in arithmetic operation"
            if not isinstance(sort_type_class(tree.left.sort), SemiringClass):
                return False, "Invalid type for arithmetic operation"
            if not isinstance(sort_type_class(tree.right.sort), SemiringClass):
                return False, "Invalid type for arithmetic operation"
            tree.sort = tree.left.sort
        elif isinstance(tree, LtNode) or isinstance(tree, GtNode) or \
             isinstance(tree, LeqNode) or isinstance(tree, GeqNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                return False, "Type mismatch in order relation"
            if not isinstance(sort_type_class(tree.left.sort), PosetClass):
                return False, "Invalid types for order relation"
            tree.sort = PredSort()
        elif isinstance(tree, EqNode) or isinstance(tree, NeqNode):
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort):
                return False, "Type mismatch in equality relation"
            # many things can be assigned/compared equal, so can't restrict types
            tree.sort = PredSort()
        elif isinstance(tree, ImpliesNode) or isinstance(tree, IffNode) or \
             isinstance(tree, AndNode) or isinstance(tree, OrNode):
            if not isinstance(tree.left.sort, PredSort) or \
               not isinstance(tree.right.sort, PredSort):
                return False, "Logical operator requires predicates"
            tree.sort = PredSort()
        elif isinstance(tree, IntersectNode) or isinstance(tree, UnionNode) or \
             isinstance(tree, DiffNode):
            lsort = tree.left.sort
            rsort = tree.right.sort
            if not isinstance(lsort, SetSort) or \
               not isinstance(rsort, SetSort):
                return False, "Arguments to set operation are not sets"
            if not sorts_compatible(screen, tl, lsort.sort, rsort.sort):
                return False, "Incompatible sets in set operation"
            tree.sort = lsort
        elif isinstance(tree, SubsetneqNode) or isinstance(tree, SubseteqNode) or \
             isinstance(tree, SupsetneqNode) or isinstance(tree, SupseteqNode):
            lsort = tree.left.sort
            rsort = tree.right.sort
            if not isinstance(lsort, SetSort) or \
               not isinstance(rsort, SetSort):
                return False, "Arguments to set relation are not sets"
            if not sorts_compatible(screen, tl, lsort.sort, rsort.sort):
                return False, "Incompatible sets in set relation"
            tree.sort = PredSort()
        elif isinstance(tree, SetBuilderNode):
            if not isinstance(tree.left.right.sort, SetSort):
                return False, "Set comprehension must range over set"
            tree.sort = tree.left.right.sort
        elif isinstance(tree, AbsNode):
            if isinstance(tree.left.sort, SetSort):
                return False, "Cannot take absolute value of set"
            if not isinstance(sort_type_class(tree.left.sort), ValuedFieldClass):
                return False, "Incompatible argument type in absolute value"
            tree.sort = tree.left.sort
        elif isinstance(tree, NegNode):
            if isinstance(tree.left.sort, SetSort):
                return False, "Cannot negate a set"
            if isinstance(tree.left.sort, PredSort):
                return False, "Cannot negate a predicate"
            if not isinstance(sort_type_class(tree.left.sort), SemiringClass):
                return False, "Invalid type for arithmetic operation"
            tree.sort = tree.left.sort
        elif isinstance(tree, NotNode):
            if not isinstance(tree.left.sort, PredSort):
                return False, "Logical negation requires predicate"
            tree.sort = PredSort()
        elif isinstance(tree, BoolNode):
            tree.sort = PredSort()
        elif isinstance(tree, ExistsNode) or isinstance(tree, ForallNode):
            tree.sort = PredSort()
        elif isinstance(tree, ElemNode):
            if not isinstance(tree.right.sort, SetSort):
                return False, "Not a set in element relation"
            if not sorts_compatible(screen, tl, tree.left.sort, tree.right.sort.sort, [], False):
                return False, "Type mismatch in element relation"
            tree.sort = PredSort()
        elif isinstance(tree, SetSort):
            if tree.sort != tree:
                ok, error = propagate(tree.sort)
                if not ok:
                    return False, error
        elif isinstance(tree, TupleSort):
            for i in range(len(tree.sorts)):
                ok, error = propagate(tree.sorts[i])
                if not ok:
                    return False, error
        return True, None
    return propagate(tree0)

def process_sorts(screen, tl):
    """
    Every move, this function is called to recompute the types of nodes in any
    quantifier zone, hypothesis or target that hasn't previously been processed
    or which has been modified since last move. A record of the last binder in
    the quantifier zone, the last hypothesis and the last target already
    processed are stored in the tableau structure and these are reset if an
    already processed line is changed.
    """
    n0, n1, n2 = tl.sorts_processed
    i = 0
    if tl.tlist0.data:
        data = tl.tlist0.data[0]
        while i < n0:
            data = data.left # skip quantifiers we already typed
            i += 1
        if data:
            ok, error = propagate_sorts_qz(screen, tl, data)
            if not ok:
                return False, error
            while data != None:
                data = data.left
                i += 1
    for j in range(n1, len(tl.tlist1.data)):
        ok, error = propagate_sorts(screen, tl, tl.tlist1.data[j])
        if not ok:
            return False, error
    for k in range(n2, len(tl.tlist2.data)):
        ok, error = propagate_sorts(screen, tl, tl.tlist2.data[k])
        if not ok:
            return False, error
    tl.sorts_processed = (i, len(tl.tlist1.data), len(tl.tlist2.data))
    return True, None

def type_vars(screen, tl):
    """
    When beginning to prove a theorem, the initial tableau needs each variable
    annotated with its constraints as defined by its corresponding binder. This
    function is called once manual or automated mode is started to do this
    annotation.
    """
    constraints = tl.constraints # all constraints of all vars
    vars = [] # vars currently in scope

    if len(tl.tlist0.data) > 0:
        qz = tl.tlist0.data[0]
    else:
        qz = None

    i = 0
    while qz != None:
        vars.append(qz.var.name())
        constraints[qz.var.name()] = qz.var.constraint
        ok, error = process_constraints(screen, tl, qz.var.constraint, constraints, vars)
        if not ok:
            screen.dialog(error)
            return
        qz = qz.left
        i += 1

    hyps = tl.tlist1.data
    for tree in hyps:
        ok, error = process_constraints(screen, tl, tree, constraints, vars)
        if not ok:
            screen.dialog(error)
            return
    tars = tl.tlist2.data
    for tree in tars:
        ok, error = process_constraints(screen, tl, tree, constraints, vars)
        if not ok:
            screen.dialog(error)
            return
    tl.constraints_processed = (i, len(tl.tlist1.data), len(tl.tlist2.data))

def update_constraints(screen, tl):
    """
    After every move, additional variables could have been added to the
    quantifier zone, or additional hypotheses or targets could have been
    added to the tableau. In such cases, this function can be called to
    annotate all variables that appear in them with their constraints.
    A count of the number of already processed binders in the quantifier
    zone, hypotheses and targets is stored in the tableau structure. This
    can be reset if a change is made to one of the already processed
    lines of the tableau.
    """
    n0, n1, n2 = tl.constraints_processed
    constraints = tl.constraints

    if len(tl.tlist0.data) > 0:
        qz = tl.tlist0.data[0]
    else:
        qz = None

    i = 0
    while i < n0: # skip already processed quantifiers
        qz = qz.left
        i += 1

    while qz != None:
        constraints[qz.var.name()] = qz.var.constraint
        ok, error = process_constraints(screen, tl, qz.var.constraint, constraints)
        if not ok:
            return False, error
        qz = qz.left
        i += 1

    hyps = tl.tlist1.data
    for j in range(n1, len(hyps)):
        ok, error = process_constraints(screen, tl, hyps[j], constraints)
        if not ok:
            return False, error
    tars = tl.tlist2.data
    for k in range(n2, len(tars)):
        ok, error = process_constraints(screen, tl, tars[k], constraints)
        if not ok:
            return False, error
    tl.constraints_processed = (i, len(hyps), len(tars))
    return True, None

def skolemize_quantifiers(tree, deps, sk, ex):
    """
    Special case of skolemize_statement which just handles the quantifier zone.
    It is supplied with a list of variables which have been skolemized, which
    it will extend with tuples of the form (name, num, flag) where name is the
    name of the variable that has been skolemized, num is the number of
    variables it depends on and flag specifies whether the variable is one of
    the original variables present in the quantifier zone when the problem was
    started.

    The skolemized variables themselves are appended to the list ex which is
    returned after removing them from the original tree.

    The function is provided with a list of variables that the skolem variable
    will depend on. Initially this is empty, but as each universally quantified
    variable is processed, it is appended to deps.

    The function returns a tuple (tree, deps, sk, ex) where tree is the new
    quantifier zone with existentials removed, deps is the list of universally
    quantified variables up to the current point, sk is the skolem tuples
    described above and ex is the list of variables that were skolemized (and
    removed from the quantifier zone; they must be added back in again when
    processed).
    """
    # find first not not skipped
    while tree and not isinstance(tree, ForallNode) and not tree.var.is_metavar and not tree.var.skolemized:
        sk.append((tree.var.name(), len(deps), True))
        ex.append(tree.var)
        tree = tree.left
    
    if not tree:
        return tree, deps, sk, ex
        
    rtree = tree # will be the returned tree

    if isinstance(tree, ForallNode):
            deps.append(tree.var)
        
    while tree.left:
        if isinstance(tree.left, ForallNode):
            deps.append(tree.left.var)
            tree = tree.left
        elif isinstance(tree.left, ExistsNode) and not tree.left.var.is_metavar and not tree.left.var.skolemized:
            sk.append((tree.left.var.name(), len(deps), True))
            ex.append(tree.left.var)
            tree.left = tree.left.left # skip this node
        else:
            tree = tree.left # nothing to do for this node

    return rtree, deps, sk, ex

#    if isinstance(tree, ExistsNode):
#        if not tree.var.is_metavar and not tree.var.skolemized: # check we didn't already deal with this var
#            sk.append((tree.var.name(), len(deps), True))
#            ex.append(tree.var)
#            return skolemize_quantifiers(tree.left, deps, sk, ex)
#        else:
#            tree.left, deps, sk, ex = skolemize_quantifiers(tree.left, deps, sk, ex)
#            return tree, deps, sk, ex
#    elif isinstance(tree, ForallNode):
#        deps.append(tree.var)
#        tree.left, deps, sk, ex = skolemize_quantifiers(tree.left, deps, sk, ex)
#        return tree, deps, sk, ex
#    else:
#        return tree, deps, sk, ex

def process_constraints(screen, tl, tree, constraints, vars=None):
    """
    Given a parse tree and a dictionary of constraints for variables, annotate
    each occurrence of variables in tree with their constraints as stored in
    the dictionary. If an existential or universal binder is encountered, the
    constraint for the variable defined will be added to the dictionary. In
    addition, if one needs a list of such variables for further processing,
    pass a list through the vars parameter and it will be appended.
    """
    def del_last(L, str):
        gen = (len(L) - 1 - i for i, v in enumerate(reversed(L)) if v == str)
        del L[next(gen, None)]

    if tree == None:
        return True, None
    elif isinstance(tree, ForallNode) \
         or isinstance(tree, ExistsNode):
        name = tree.var.name()
        if vars != None:
            vars.append(name)
        constraints[tree.var.name()] = tree.var.constraint
        ok, error = process_constraints(screen, tl, tree.var.constraint, constraints, vars)
        if not ok:
            return False, error
        ok, error = process_constraints(screen, tl, tree.left, constraints, vars)
        if vars != None:
            del_last(vars, name)
        if not ok:
            return False, error
    elif isinstance(tree, SetBuilderNode):
        name = tree.left.left.name()
        if vars != None:
            vars.append(name)
        new_varname = new_variable(screen, tl, 'X') # introduce fake universe for inference
        X = VarNode(new_varname)
        X.is_metavar = True
        X.constraint = SetSort(Universum())
        constraints[tree.left.left.name()] = X
        ok, error = process_constraints(screen, tl, tree.left, constraints, vars)
        if not ok:
            if vars != None:
                del_last(vars, name)
            return False, error
        ok, error = process_constraints(screen, tl, tree.right, constraints, vars)
        if vars != None:
            del_last(vars, name)
        if not ok:
            return False, error
    elif isinstance(tree, VarNode):
        varnames = vars if vars != None else constraints
        if not tree.name() in varnames:
            if tree.name() not in system_unary_functions and \
               tree.name() not in system_binary_functions and \
               tree.name() not in system_predicates:
               return False, f"Unknown variable/function {tree.name()}"
        else:
            tree.constraint = constraints[tree.name()]
    elif isinstance(tree, LRNode):
        ok, error = process_constraints(screen, tl, tree.left, constraints, vars)
        if not ok:
            return False, error
        ok, error = process_constraints(screen, tl, tree.right, constraints, vars)
        if not ok:
            return False, error
    elif isinstance(tree, FnApplNode):
        ok, error = process_constraints(screen, tl, tree.var, constraints, vars)
        if not ok:
            return False, error
        for v in tree.args:
            ok, error = process_constraints(screen, tl, v, constraints, vars)
            if not ok:
                return False, error
    elif isinstance(tree, TupleNode):
        for v in tree.args:
            ok, error = process_constraints(screen, tl, v, constraints, vars)
            if not ok:
                return False, error
    elif isinstance(tree, SymbolNode):
         ok, error = process_constraints(screen, tl, tree.constraint, constraints, vars)
         if not ok:
             return False, error
    elif isinstance(tree, FunctionConstraint):
         ok, error = process_constraints(screen, tl, tree.domain, constraints, vars)
         if not ok:
             return False, error
         ok, error = process_constraints(screen, tl, tree.codomain, constraints, vars)
         if not ok:
             return False, error
    elif isinstance(tree, DomainTuple):
         for v in tree.sets:
             ok, error = process_constraints(screen, tl, v, constraints, vars)
         if not ok:
             return False, error
    return True, None

def skolemize_statement(screen, tree, deps, depmin, sk, qz, mv, positive, blocked=False):
    """
    Given a statement, tree, return a version of it in which all variables that
    have been skolemized so far, as specified by sk, are replaced with
    appropriate function applications.

    The function also removes any existentials from the prefix of the statement
    and adds them to sk.

    The function also creates metavariables, depending whether we are in positive
    position or not (targets are overall in positive positition, but being on the
    left side of an implication also changes the position). The metavariables are
    appended to the list mv.

    The function is supplied with a list, deps, of variables that skolem functions
    depend on up to this point (described in more detail in the function above).
    The number depmin optionally skips some number of these.

    Occasionally, we decide to not remove all quantifiers from a statement and
    this is indicated by setting blocked=True. From this point on, no further
    quantifiers will be removed.

    The rules are as follows for each position/quantifier combination:
       * negative/forall => metavariable
       * negative/exists => skolem
       * positive/forall => nothing
       * positive/exists => skolem metavariable
    """
    d = len(deps)
    s = len(sk)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()
    
    if isinstance(tree, NotNode) and isinstance(tree.left, EqNode):
        neq = NeqNode(tree.left.left, tree.left.right)
        neq.sort = PredSort # may be replacing an already typed node
        return neq
    if isinstance(tree, OrNode):
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, True)
        tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, True)
        return tree
    elif isinstance(tree, ForallNode):
        is_blocked = blocked
        if not blocked:
            if positive:
                deps.append(tree.var)
                qz.append(tree)
            else:
                if not isinstance(tree.left, ImpliesNode) and not \
                       isinstance(tree.left, OrNode):
                    tree.var.is_metavar = True
                    deps.append(tree.var)
                    mv.append(tree.var.name())
                    qz.append(ExistsNode(tree.var, None))
                else:
                    is_blocked = True
        tree.var.constraint = skolemize_statement(screen, tree.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, is_blocked or isinstance(tree.left, IffNode))
        rollback()
        return tree.left if not is_blocked else tree    
    elif isinstance(tree, ExistsNode):
        is_blocked = blocked
        if not blocked:
            sk.append((tree.var.name(), len(deps), False))
            domain_constraints = [v.var.constraint if isinstance(v, ForallNode) else v.constraint for v in deps[depmin:]]
            if len(domain_constraints) > 1:
                fn_constraint = FunctionConstraint(DomainTuple(domain_constraints), SetOfNode(tree.var.constraint))
            elif len(domain_constraints) == 1:
                fn_constraint = FunctionConstraint(domain_constraints[0], SetOfNode(tree.var.constraint))
            else:
                fn_constraint = FunctionConstraint(None, SetOfNode(tree.var.constraint))
            if positive:
                if not blocked:
                    tree.var.is_metavar = True
                    mv.append(tree.var.name())
                    v = VarNode(tree.var.name(), fn_constraint, True)
                    qz.append(ExistsNode(v, None))
                if isinstance(tree.left, ImpliesNode) or isinstance(tree.left, OrNode):
                    is_blocked = True
            else:
                v = VarNode(tree.var.name(), fn_constraint, False)
                qz.append(ForallNode(v, None))
        tree.var.constraint = skolemize_statement(screen, tree.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, is_blocked)
        rollback()
        return tree.left if not blocked else tree
    elif isinstance(tree, SetBuilderNode):
        if not blocked:
            if positive:
                deps.append(tree.left.left)
            else:
                tree.left.left.is_metavar = True
                deps.append(tree.left.left) # free
                mv.append(tree.left.left.name())
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, blocked)
        tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, IffNode) or isinstance(tree, ImpliesNode):
        is_blocked = blocked or isinstance(tree, IffNode)
        t = tree
        while isinstance(t.left, ForallNode) or isinstance(t.left, ExistsNode):
            t.left.var.constraint = skolemize_statement(screen, t.left.var.constraint, deps, depmin, sk, qz, mv, not positive, is_blocked)
            t = t.left
        t.left = skolemize_statement(screen, t.left, deps, depmin, sk, qz, mv, not positive, is_blocked)
        if not isinstance(tree.right, ForallNode) and not isinstance(tree.right, ExistsNode):
            tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, is_blocked)
        else:
            tree.right.var.constraint = skolemize_statement(screen, tree.right.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
            t = tree.right
            while isinstance(t.left, ForallNode) or isinstance(t.left, ExistsNode):
                t.left.var.constraint = skolemize_statement(screen, t.left.var.constraint, deps, depmin, sk, qz, mv, positive, is_blocked)
                t = t.left
            t.left = skolemize_statement(screen, t.left, deps, depmin, sk, qz, mv, positive, is_blocked)
        rollback()
        return tree
    elif isinstance(tree, LRNode):
        tree.left = skolemize_statement(screen, tree.left, deps, depmin, sk, qz, mv, positive, blocked)
        tree.right = skolemize_statement(screen, tree.right, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, VarNode):
        is_meta = False
        if tree.name() in mv:
            is_meta = True
            tree.is_metavar = True
        n, is_orig = skolem_deps(tree.name(), sk)
        if n == -1: # not a skolem variable
            return tree
        else:
            depstart = 0 if is_orig else depmin
            fn_args = [VarNode(deps[i].name(), deps[i].constraint, deps[i].is_metavar) \
                    for i in range(depstart, n)]
            fn = FnApplNode(VarNode(tree.name()), fn_args)
            fn.is_skolem = True
            if is_meta:
                fn.is_metavar = True
                fn.var.is_metavar = True
            fn.sort = tree.sort # may be replacing an already typed node
            fn.var.sort = tree.sort # may be replacing an already typed node
            return fn
    elif isinstance(tree, FnApplNode):
        if tree.name() in mv:
            tree.is_metavar = True
            tree.var.is_metavar = True
        n, is_orig = skolem_deps(tree.name(), sk)
        if n != -1 and not tree.is_skolem: # skolem variable not already skolemized
            tree.var = skolemize_statement(screen, tree.var, deps, depmin, sk, qz, mv, positive, blocked)
            rollback()
        for i in range(0, len(tree.args)):
            tree.args[i] = skolemize_statement(screen, tree.args[i], deps, depmin, sk, qz, mv, positive, blocked)
            rollback()
        return tree
    elif isinstance(tree, TupleNode):
        for i in range(0, len(tree.args)):
            tree.args[i] = skolemize_statement(screen, tree.args[i], deps, depmin, sk, qz, mv, positive, blocked)
            rollback()
        return tree
    elif isinstance(tree, SetSort):
        tree.sort = skolemize_statement(screen, tree.sort, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, TupleSort):
        for i in range(len(tree.sorts)):
            tree.sorts[i] = skolemize_statement(screen, tree.sorts[i], deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, CartesianConstraint):
        for i in range(len(tree.sorts)):
            tree.sorts[i] = skolemize_statement(screen, tree.sorts[i], deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, FunctionConstraint):
        tree.domain = skolemize_statement(screen, tree.domain, deps, depmin, sk, qz, mv, positive, blocked)
        tree.codomain = skolemize_statement(screen, tree.codomain, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, DomainTuple):
        for i in range(len(tree.sets)):
             tree.sets[i] = skolemize_statement(screen, tree.sets[i], deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset':
        tree.constraint = skolemize_statement(screen, tree.constraint, deps, depmin, sk, qz, mv, positive, blocked)
        rollback()
        return tree
    else:
        return tree
        
def skolem_deps(name, sk):
    """
    Look up variable with the given name in the skolem tuple list sk. If found
    return the data n, is_orig associated with that variable in sk. Otherwise,
    return -1, False.
    """
    for (v, n, is_orig) in sk:
        if v == name:
            return n, is_orig
    return -1, False
