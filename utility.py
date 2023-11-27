from nodes import ForallNode, ExistsNode, FnApplNode, VarNode, SetBuilderNode, \
     LRNode, TupleNode, SymbolNode, NotNode, EqNode, NeqNode, GtNode, LtNode, \
     LeqNode, GeqNode, AndNode, OrNode, IffNode, ImpliesNode, UnionNode, \
     IntersectNode, DiffNode, CartesianNode, SetOfNode, NaturalNode, ExpNode, \
     CircNode, TupleComponentNode, PowerSetNode, AddNode, SubNode, MulNode, \
     DivNode, SubsetneqNode, SubseteqNode, SupsetneqNode, SupseteqNode, \
     AbsNode, NegNode, ElemNode, BoolNode, DeadNode, LambdaNode
from sorts import SetSort, TupleSort, FunctionConstraint, DomainTuple, \
     CartesianConstraint, Universum, NumberSort, PredSort
from typeclass import CompleteValuedFieldClass, CompleteOrderedValuedFieldClass, \
     FieldClass, OrderedRingClass, OrderedSemiringClass
from copy import deepcopy, copy
from heapq import merge  

system_unary_functions = ['complement', 'universe']
system_binary_functions = ['min', 'max']
system_predicates = ['is_bounded', 'is_upper_bound', 'is_lower_bound', 'is_supremum', \
                     'is_infimum', 'is_pair', 'is_function', 'is_injective', \
                     'is_surjective', 'is_bijective']

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

def qz_copy_var(screen, tl, extras, name, new_name):
    """
    Make a copy, in the quantifier zone of the tableau, of the variable with
    the given name. The copy will be given the new_name specified, but type
    information and any flags attached to the variable will be kept the same.

    In addition, a list of existential or universal quantifiers may be
    specified which are missing from the quantifier zone, but which should be
    added (after renaming) if their name is the one specified.

    The function is safe to call multiple times with the same name, as it
    ignores variables it has already copied under the new name supplied.
    """
    node_to_copy = None
    qz = tl.tlist0.data[0]
    tree = qz

    for v in extras: # extra variables to rename, from unquantify
       if isinstance(v, ExistsNode) or isinstance(v, ForallNode):
          if v.var.name() == name: # found the relevant variable
              node_to_copy = v

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
       tree = tree.left
    screen.pad0.pad[0] = str(qz)
    screen.pad0.refresh()
    screen.focus.refresh()
       
def relabel(screen, tl, extras, tree, update_qz=False, temp=False):
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
                    qz_copy_var(screen, tl, extras, name, new_name)
            elif not constraint and tree.is_metavar:
                new_name = relabel_varname(name, tldict)
                vars_dict[name] = new_name
                tree._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name)
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
                    qz_copy_var(screen, tl, extras, name, new_name)
            elif tree.is_metavar:
                new_name = relabel_varname(name, tldict)
                vars_dict[name] = new_name
                tree.var._name = new_name
                if update_qz:
                    qz_copy_var(screen, tl, extras, name, new_name)
            else:
                process(tree.var, constraint)
            for v in tree.args:
                process(v, constraint)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                process(v, constraint)
        elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset':
            process(tree.constraint, constraint)
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
    return tree

def relabel_constraints(screen, tl, tree):
    """
    Hopefully this function will go away eventually. It is solely for
    relabeling universums as a hack instead of type inferring a universe.
    """
    vars_dict = dict()
    tldict = tl.vars # current subscripts

    def process(tree):
        if tree == None:
            return
        if isinstance(tree, Universum):
            name = tree.name()
            if name == '\\mathcal{U}':
                if name in vars_dict:
                    tree._name = vars_dict[name]
                else:
                    new_name = relabel_varname(name, tldict)
                    vars_dict[name] = new_name
                    tree._name = new_name
                    s = SortNode(tree) # insert new sort for new metavar universum
                    s.subsorts.append(tl.stree)
                    tl.stree = s
        if isinstance(tree, ForallNode) or isinstance(tree, ExistsNode):
            process(tree.var.constraint)
            process(tree.left)
        elif isinstance(tree, VarNode):
            process(tree.constraint)
        elif isinstance(tree, SetBuilderNode):
            process(tree.left)
            process(tree.right)
        elif isinstance(tree, LRNode):
            process(tree.left)
            process(tree.right)
        elif isinstance(tree, FnApplNode):
            process(tree.var)
            for v in tree.args:
                process(v)
        elif isinstance(tree, TupleNode):
            for v in tree.args:
                process(v)
        elif isinstance(tree, SymbolNode) and tree.name() == '\\emptyset' and \
                      isinstance(tree.sort, VarNode):
            process(tree.sort)
        elif isinstance(tree, SetSort):
            process(tree.sort)
        elif isinstance(tree, FunctionConstraint):
            process(tree.domain)
            process(tree.codomain)
        elif isinstance(tree, CartesianConstraint):
            for v in tree.sorts:
                process(v)
        elif isinstance(tree, DomainTuple):
            for v in tree.sets:
                process(v)
            for v in tree.sort.sets:
                process(v)

    process(tree)
    return tree

def append_tree(tlist, stmt, dirty):
    """
    Append the given statement to the given tree list. This is used to add a
    hypothesis or target. The function is supplied with a list, dirty, of all
    the line numbers of the tableau that must be updated. We append the
    relevant line number to this list.
    """
    n = len(tlist)
    tlist.append(stmt)
    if dirty != None:
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
    if dirty != None:
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

def metavars_used(tree):
    """
    Given a parsed statement, return a list of names of metavariables (as
    strings) that occur in the given statement.
    """
    used = []

    def search(tree):
        if tree == None:
            return
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

def add_descendant(ttree, i, j):
    """
    Find target i in the given target tree and add a descendent j. This is
    done when proving target j will be sufficient to prove target i, e.g.
    because we reasoned backwards to j from i.
    """
    if ttree.num == i:
        ttree.andlist = [TargetNode(j)]
        return True
    for P in ttree.andlist:
        if add_descendant(P, i, j):
            return True
    return False

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
        self.subsorts = []

def initialise_sorts(screen, tl):
    """
    Initialise the internally maintained sort graph. At the top is the sort
    \mathcal{U} and we add all the number types to this sort graph with the
    obvious inclusions.
    """
    stree = SortNode(Universum())
    tl.stree = stree 
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

def find_sort(screen, tl, stree, s):
    """
    Given the tree of sorts, stree, find the sort s (as a node) in the tree.
    If it is not found, return False.
    """
    if sorts_equal(s, stree.sort):
        return stree
    for t in stree.subsorts:
        r = find_sort(screen, tl, t, s)
        if r:
            return r
    return None

def insert_sort(screen, tl, s1, s2):
    """
    Make s2 a subsort of s1 by adding it to the internally maintained sort
    tree in the appropriate location. It is assumed that the sort s1 already
    exists in the tree.
    """
    r = find_sort(screen, tl, tl.stree, s1)
    r.subsorts.append(SortNode(s2))

def sorts_equal(s1, s2):
    """
    Return True if two sorts are equal, else return False.
    """
    if type(s1) != type(s2):
        return False
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
        NaturalNode : '\\mathbb{N}',
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
        ImpliesNode : '\\implies',
        IffNode : '\\iff',
        AndNode : '\\wedge',
        OrNode : '\\vee',
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
        NotNode : '\\neg',
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

def get_constants(screen, tl, tree):
    """
    Given a parse tree, return a list of all constants used in the statement,
    i.e. excluding all variable names but including function names which are
    meaningful to the system. Each name appears once and the list will be
    sorted.
    """
    constants = []
    
    def process(tree):
        if tree == None:
            return
        if isinstance(tree, SymbolNode):
            append_unique(constants, tree.name())
        elif isinstance(tree, VarNode) or isinstance(tree, SetOfNode) \
          or isinstance(tree, DeadNode) or isinstance(tree, LambdaNode) \
          or isinstance(tree, ForallNode) or isinstance(tree, ExistsNode) \
          or isinstance(tree, Universum):
            pass
        elif isinstance(tree, FnApplNode):
            if isinstance(tree.var, VarNode):
                name = tree.var.name()
                if (name in system_unary_functions) or \
                   (name in system_binary_functions) or \
                   (name in system_predicates):
                    append_unique(constants, name)
        elif isinstance(tree, TupleNode):
            append_unique(constants, 'Tuple('+str(len(tree.args))+')')
        elif isinstance(tree, NumberSort):
            append_unique(constants, tree.name())
        elif isinstance(tree, TupleSort):
            append_unique(constants, 'Tuple('+str(len(tree.sorts))+')')
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
    if isinstance(tree, ExistsNode):
        if not tree.var.is_metavar and not tree.var.skolemized: # check we didn't already deal with this var
            sk.append((tree.var.name(), len(deps), True))
            ex.append(tree.var)
            return skolemize_quantifiers(tree.left, deps, sk, ex)
        else:
            tree.left, deps, sk, ex = skolemize_quantifiers(tree.left, deps, sk, ex)
            return tree, deps, sk, ex
    elif isinstance(tree, ForallNode):
        deps.append(tree.var)
        tree.left, deps, sk, ex = skolemize_quantifiers(tree.left, deps, sk, ex)
        return tree, deps, sk, ex
    else:
        return tree, deps, sk, ex

def process_constraints(screen, tree, constraints, vars=None):
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
        return True
    elif isinstance(tree, ForallNode) \
         or isinstance(tree, ExistsNode):
        name = tree.var.name()
        if vars != None:
            vars.append(name)
        constraints[tree.var.name()] = tree.var.constraint
        ok, error = process_constraints(screen, tree.var.constraint, constraints, vars)
        if not ok:
            return False, error
        ok, error = process_constraints(screen, tree.left, constraints, vars)
        if vars != None:
            del_last(vars, name)
        if not ok:
            return False, error
    elif isinstance(tree, SetBuilderNode):
        name = tree.left.left.name()
        if vars != None:
            vars.append(name)
        constraints[tree.left.left.name()] = tree.left.left.constraint
        ok, error = process_constraints(screen, tree.left, constraints, vars)
        if not ok:
            if vars != None:
                del_last(vars, name)
            return False, error
        ok, error = process_constraints(screen, tree.right, constraints, vars)
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
        ok, error = process_constraints(screen, tree.left, constraints, vars)
        if not ok:
            return False, error
        ok, error = process_constraints(screen, tree.right, constraints, vars)
        if not ok:
            return False, error
    elif isinstance(tree, FnApplNode):
        ok, error = process_constraints(screen, tree.var, constraints, vars)
        if not ok:
            return False, error
        for v in tree.args:
            ok, error = process_constraints(screen, v, constraints, vars)
            if not ok:
                return False, error
    elif isinstance(tree, TupleNode):
        for v in tree.args:
            ok, error = process_constraints(screen, v, constraints, vars)
            if not ok:
                return False, error
    elif isinstance(tree, SymbolNode):
         ok, error = process_constraints(screen, tree.constraint, constraints, vars)
         if not ok:
             return False, error
    elif isinstance(tree, FunctionConstraint):
         ok, error = process_constraints(screen, tree.domain, constraints, vars)
         if not ok:
             return False, error
         ok, error = process_constraints(screen, tree.codomain, constraints, vars)
         if not ok:
             return False, error
    elif isinstance(tree, DomainTuple):
         for v in tree.sets:
             ok, error = process_constraints(screen, v, constraints, vars)
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
