from utility import is_implication, get_constants, get_init_vars, list_merge, deps_compatible, \
     TargetNode, update_constraints, process_sorts, append_tree, unquantify, target_compatible, \
     append_quantifiers, relabel
from autoparse import parse_consts
from moves import targets_proved
from unification import unify
from nodes import DeadNode, AutoImplNode, AutoEqNode, ImpliesNode, AndNode
from tree import TreeList
from copy import deepcopy
import logic

class AutoData:
    def __init__(self, line, version, const1, const2):
        self.line = line # line in the hypothesis or target pane
        self.version = version # how many times has this line been changed
        self.const1 = const1 # constants on left side of implication or constants in predicate
        self.const2 = const2 # constants on right side of implication
        self.applied = [] # list of heads that have been applied to this 

    def __str__(self):
        return str(self.line)

    def __repr__(self):
        return repr(self.line)

class AutoTab:
    def __init__(self, screen, tl):
        tlist0 = tl.tlist0.data
        tlist1 = tl.tlist1.data
        tlist2 = tl.tlist2.data
        self.tl = tl
        self.nhyps = len(tlist1)
        self.ntars = len(tlist2)
        self.vars = get_init_vars(screen, tl, tlist0[0]) if tlist0 else [] # vars in initial tableau
        qz_data = [AutoData(0, 0, get_constants(screen, tl, tlist0[0]), None)] if tlist0 else []
        hyp_heads = []
        hyp_impls = []
        tar_heads = []
        for i in range(len(tlist1)):
            v = tlist1[i]
            if is_implication(v):
                v, univs = unquantify(screen, v, False)
                c1 = get_constants(screen, tl, v.left)
                c2 = get_constants(screen, tl, v.right)
                hyp_impls.append(AutoData(i, 0, c1, c2))
            else:
                c = get_constants(screen, tl, v)
                hyp_heads.append(AutoData(i, 0, c, None))
        for j in range(len(tlist2)):
           v = tlist2[j]
           c = get_constants(screen, tl, v)
           tar_heads.append(AutoData(j, 0, c, None))
        self.hyp_heads = hyp_heads
        self.hyp_impls = hyp_impls
        self.tar_heads = tar_heads
        self.thms = []

def update_autotab(screen, tl, atab, dirty1, dirty2):
    """
    Given an AutoTab data structure and a list of modified/added hypotheses
    (dirty1) and a list of modified/added targets (dirty2), update the data
    in the AutoTab structure to reflect current reality.
    """
    tlist0 = tl.tlist0.data
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    for i in dirty1:
        version = -1
        if i < atab.nhyps: # delete old hypothesis
            j = 0
            while j < len(atab.hyp_heads):
                t = atab.hyp_heads[j]
                if t.line == i:
                    version = atab.hyp_heads[j].version
                    del atab.hyp_heads[j]
                else:
                    j += 1
            j = 0
            while j < len(atab.hyp_impls):
                t = atab.hyp_impls[j]
                if t.line == i:
                    version = atab.hyp_impls[j].version
                    del atab.hyp_impls[j]
                else:
                    j += 1
        # add new details
        v = tlist1[i]
        if is_implication(v):
            v, univs = unquantify(screen, v, False)
            c1 = get_constants(screen, tl, v.left)
            c2 = get_constants(screen, tl, v.right)
            atab.hyp_impls.append(AutoData(i, version + 1, c1, c2))
        else:
            c = get_constants(screen, tl, v)
            atab.hyp_heads.append(AutoData(i, version + 1, c, None))
    for j in dirty2:
        version = -1
        if j < atab.ntars: # delete old target
            k = 0
            while k < len(atab.tar_heads):
                t = atab.tar_heads[k]
                if t.line == j:
                    version = atab.tar_heads[j].version
                    del atab.tar_heads[k]
                else:
                    k += 1
        # add new details
        v = tlist2[j]
        c = get_constants(screen, tl, v)
        atab.tar_heads.append(AutoData(j, version + 1, c, None))
    atab.nhyps = len(tlist1)
    atab.ntars = len(tlist2)

def create_index(screen, tl):
    """
    Read the library in and create an index of all theorems and definitions up
    to but not including the theorem we are trying to prove.
    """
    library = open("library.dat", "r")
    index = []
    title = library.readline()
    while title: # check for EOF
        title = title[7:-1]
        const_str = library.readline()[0:-1]
        success, consts = parse_consts(screen, const_str)
        if not success:
            screen.dialog(consts)
            screen.dialog(title)
            break
        term_str = library.readline()[0:-1]
        tags = library.readline() # skip tags
        filepos = library.tell()
        if filepos == tl.loaded_theorem:
            break
        index.append((title, consts, filepos))
        while title != '\n':
            title = library.readline()
        title = library.readline()
    return index

def get_autonode(screen, alist, line):
    """
    Given a list of AutoData structs, find the one with the given line if it
    exists and return it. Otherwise, return None.
    """
    for k in range(len(alist)):
        if alist[k].line == line:
            return alist[k]
    return None

def filter_theorems1(screen, index, consts):
    """
    Given a library index, filter out theorems all of whose precedents
    contain only constants in the given list.
    """
    thms = []
    for (title, c, filepos) in index:
        thmlist = c[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            if isinstance(thm, AutoImplNode):
                tc = thm.left
                if set(tc).issubset(consts):
                    thms.append((title, c, filepos, i))
    return thms

def filter_theorems2(screen, index, consts):
    """
    Given a library index, filter out theorems all of whose conclusions
    contain only constants in the given list.
    """
    thms = []
    for (title, c, filepos) in index:
        thmlist = c[2]
        for i in range(len(thmlist)):
            thm = thmlist[i]
            if isinstance(thm, AutoImplNode):
                tc = thm.right
                if set(tc).issubset(consts):
                    thms.append((title, c, filepos, i))
    return thms

def autocleanup(screen, tl, ttree):
    dirty1, dirty2 = logic.cleanup(screen, tl, ttree)
    logic.fill_macros(screen, tl)
    ok, error = update_constraints(screen, tl)
    if ok:
        ok, error = process_sorts(screen, tl)
        if not ok:
            screen.dialog(error)
    else:
        screen.dialog(error)
    return dirty1, dirty2

def update_screen(screen, tl):
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    pad1 = screen.pad1.pad
    pad2 = screen.pad2.pad
    screen.pad0.pad[0] = str(tl.tlist0.data[0])
    for i in range(len(tlist1)):
        pad1[i] = str(tlist1[i])
    for i in range(len(tlist2)):
        pad2[i] = str(tlist2[i])
    tl.tlist1.line = screen.pad1.scroll_line + screen.pad1.cursor_line
    tl.tlist2.line = screen.pad2.scroll_line + screen.pad2.cursor_line
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def automate(screen, tl, ttree):
    libthms_loaded = dict() # keep track of which library theorems we loaded, and where
    fake_ttree = TargetNode(-1, []) # used for fake loading of library results
    tlist1 = tl.tlist1.data
    tlist2 = tl.tlist2.data
    atab = AutoTab(screen, tl) # initialise automation data structure
    index = create_index(screen, tl)
    done = False # whether all targets are proved
    while True: # keep going until theorem proved or progress stalls
        # get next unproved target
        i = 0
        made_progress = False
        while i < len(tlist2):
            while i < len(tlist2):
                if not isinstance(tlist2[i], DeadNode):
                    break
                i += 1
            if i >= len(tlist2):
                break
            # find all target compatible hypotheses
            hyps = []
            for j in range(len(tlist1)):
                if deps_compatible(screen, tl, ttree, i, j):
                    hyps.append(j)
            # find all consequences of individual hypotheses (Fredy's ball)
            hprogress = False # whether some progress is made on the hypothesis side
            for j in hyps:
                hyp = get_autonode(screen, atab.hyp_heads, j)
                if hyp: # hypothesis is a head
                    progress = False
                    line2 = hyp.line
                    hc = hyp.const1
                    # first check if any hyp_impls can be applied to head
                    for imp in atab.hyp_impls:
                        if set(imp.const1).issubset(hc):
                            unifies = False
                            line1 = imp.line
                            if (hyp.line, hyp.version, True) not in imp.applied:
                                imp.applied.append((hyp.line, hyp.version, True))
                                thm = tlist1[line1]
                                thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                if isinstance(thm, ImpliesNode):
                                    prec, u = unquantify(screen, thm.left, True)
                                    if not isinstance(prec, AndNode):
                                        # check if precedent unifies with hyp
                                        unifies, assign, macros = unify(screen, tl, prec, tlist1[line2])
                            if unifies:
                                # apply modus ponens
                                dep = tl.tlist1.dependency(line1)
                                dep = target_compatible(screen, tl, ttree, dep, line2, True)
                                if dep:
                                    success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], True)
                                    if success:
                                        hprogress = True
                                        progress = True
                                        update_autotab(screen, tl, atab, dirty1, dirty2)
                                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                        update_autotab(screen, tl, atab, dirty1, dirty2)
                                        done, plist = targets_proved(screen, tl, ttree)
                                        if done:
                                            screen.dialog("All targets proved!")
                                            update_screen(screen, tl)
                                            return
                    # if no progress, look for library result that can be applied to head
                    if not progress:
                        libthms = filter_theorems1(screen, index, hc)
                        for (title, c, filepos, line) in libthms:
                            # check to see if thm already loaded
                            unifies = False
                            if filepos in libthms_loaded:
                                j = libthms_loaded[filepos] # get position loaded in tableau
                                tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                if tnode and (hyp.line, hyp.version, True) not in tnode.applied:
                                    tnode.applied.append((hyp.line, hyp.version, True))
                                    thm = tlist1[j + line]
                                    thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                    if isinstance(thm, ImpliesNode):
                                        prec, u = unquantify(screen, thm.left, True)
                                        if not isinstance(prec, AndNode):
                                            # check if precedent unifies with hyp
                                            unifies, assign, macros = unify(screen, tl, prec, tlist1[line2])
                            else: # library theorem not yet loaded
                                fake_tl = TreeList()
                                fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
                                fake_tl.stree = deepcopy(tl.stree) # copy sort tree from tl
                                library = open("library.dat", "r")
                                logic.library_import(screen, fake_tl, library, filepos)
                                library.close()
                                autocleanup(screen, fake_tl, fake_ttree)
                                thm = fake_tl.tlist1.data[line]
                                # check theorem has only one precedent
                                thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                if isinstance(thm, ImpliesNode):
                                    prec, u = unquantify(screen, thm.left, True)
                                    if not isinstance(prec, AndNode):
                                        # check if precedent unifies with hyp
                                        unifies, assign, macros = unify(screen, fake_tl, prec, tlist1[line2])
                                        if unifies:
                                            # transfer library result to tableau
                                            dirty1 = []
                                            dirty2 = []
                                            j = len(tlist1)
                                            fake_tlist0 = fake_tl.tlist0.data
                                            if fake_tlist0:
                                                append_quantifiers(tl.tlist0.data, fake_tlist0[0])
                                            fake_list1 = fake_tl.tlist1.data
                                            for k in range(len(fake_list1)):
                                                append_tree(tlist1, fake_list1[k], dirty1)
                                            libthms_loaded[filepos] = j
                                            tl.vars = fake_tl.vars
                                            tl.stree = fake_tl.stree
                                            update_autotab(screen, tl, atab, dirty1, dirty2)
                                            tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                            tnode.applied.append((hyp.line, hyp.version, True))
                            if unifies:
                                line1 = j + line
                                # apply modus ponens
                                dep = tl.tlist1.dependency(line1)
                                dep = target_compatible(screen, tl, ttree, dep, line2, True)
                                if dep:
                                    success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], True)
                                    if success:
                                        hprogress = True
                                        update_autotab(screen, tl, atab, dirty1, dirty2)
                                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                        update_autotab(screen, tl, atab, dirty1, dirty2)
                                        done, plist = targets_proved(screen, tl, ttree)
                                        if done:
                                            screen.dialog("All targets proved!")
                                            update_screen(screen, tl)
                                            return
            if not done:
                # check if constants in target are all in hypotheses
                tar = get_autonode(screen, atab.tar_heads, i)
                tarc = tar.const1
                hypc = []
                heads = [] # list of autonodes for target compatible hyp_heads
                impls = [] # list of autonodes for target compatible hyp_impls
                for k in hyps:
                    node = get_autonode(screen, atab.hyp_heads, k)
                    if node:
                        heads.append(node)
                        c = node.const1
                    else:
                        node = get_autonode(screen, atab.hyp_impls, k)
                        impls.append(node)
                        c = list_merge(node.const1, node.const2)
                    hypc = list_merge(hypc, c)
                tprogress = False # whether or not some progress is made on the target side
                if not set(tarc).issubset(hypc):
                    pass # not implemented yet
                else: # it is possible that the target can be directly proved from the hyps
                    # check if some implication among the hyps can be used
                    for imp in impls:
                        if (tar.line, tar.version, False) not in imp.applied: # not yet applied to this head
                            # check if this implication can be applied to this head
                            pass # not implemented yet
                # try to find a theorem that applies to the target
                if not tprogress:
                    libthms = filter_theorems2(screen, index, tarc)
                    for (title, c, filepos, line) in libthms:
                        implc = c[2][line].left
                        # check to see if constants of libthm are among the hyp constants hypc
                        if set(implc).issubset(hypc) or not hypc:
                            # check to see if thm already loaded
                            line2 = tar.line
                            unifies = False
                            if filepos in libthms_loaded:
                                j = libthms_loaded[filepos] # get position loaded in tableau
                                tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                if tnode and (tar.line, tar.version, False) not in tnode.applied:
                                    tnode.applied.append((tar.line, tar.version, False))
                                    thm = tlist1[j + line]
                                    thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                    if isinstance(thm, ImpliesNode):
                                        thm = relabel(screen, tl, univs, thm, True)
                                        prec, u = unquantify(screen, thm.right, False)
                                        if not isinstance(prec, AndNode):
                                            # check if precedent unifies with hyp
                                            unifies, assign, macros = unify(screen, tl, prec, tlist2[line2])
                            else: # library theorem not yet loaded
                                fake_tl = TreeList()
                                fake_tl.vars = deepcopy(tl.vars) # copy variable subscript record from tl
                                fake_tl.stree = deepcopy(tl.stree) # copy sort tree from tl
                                library = open("library.dat", "r")
                                logic.library_import(screen, fake_tl, library, filepos)
                                library.close()
                                autocleanup(screen, fake_tl, fake_ttree)
                                if line >= len(fake_tl.tlist1.data):
                                    for i in range(len(fake_tl.tlist1.data)):
                                        screen.dialog(str(i)+" : "+str(fake_tl.tlist1.data[i]))
                                thm = fake_tl.tlist1.data[line]
                                thm, univs = unquantify(screen, thm, False) # remove quantifiers by taking temporary metavars
                                # check theorem has only one precedent
                                if isinstance(thm, ImpliesNode):
                                    thm = relabel(screen, fake_tl, univs, thm, True)
                                    prec, u = unquantify(screen, thm.right, False)
                                    if not isinstance(prec, AndNode):
                                        # check if precedent unifies with hyp
                                        unifies, assign, macros = unify(screen, fake_tl, prec, tlist2[line2])
                                        if unifies:
                                            # transfer library result to tableau
                                            dirty1 = []
                                            dirty2 = []
                                            j = len(tlist1)
                                            fake_tlist0 = fake_tl.tlist0.data
                                            if fake_tlist0:
                                                append_quantifiers(tl.tlist0.data, fake_tlist0[0])
                                            fake_list1 = fake_tl.tlist1.data
                                            for k in range(len(fake_list1)):
                                                append_tree(tlist1, fake_list1[k], dirty1)
                                            libthms_loaded[filepos] = j
                                            tl.vars = fake_tl.vars
                                            tl.stree = fake_tl.stree
                                            update_autotab(screen, tl, atab, dirty1, dirty2)
                                            tnode = get_autonode(screen, atab.hyp_impls, j + line)
                                            tnode.applied.append((tar.line, tar.version, False))
                            if unifies:
                                line1 = j + line
                                # apply modus ponens
                                dep = tl.tlist1.dependency(line1)
                                dep = target_compatible(screen, tl, ttree, dep, line2, False)
                                if dep:
                                    success, dirty1, dirty2 = logic.modus_ponens(screen, tl, ttree, dep, line1, [line2], False)
                                    if success:
                                        tprogress = True
                                        update_autotab(screen, tl, atab, dirty1, dirty2)
                                        dirty1, dirty2 = autocleanup(screen, tl, ttree)
                                        update_autotab(screen, tl, atab, dirty1, dirty2)
                                        done, plist = targets_proved(screen, tl, ttree)
                                        if done:
                                            screen.dialog("All targets proved!")
                                            update_screen(screen, tl)
                                            return
            if tprogress or not hprogress: # must move on if theorem reasoned back from
                i += 1
            if hprogress or tprogress:
                made_progress = True
        if not made_progress: # we aren't getting anywhere
            screen.dialog("Unable to prove theorem automatically")
            update_screen(screen, tl)
            return

        