from copy import deepcopy
from nodes import ForallNode, ExistsNode, ImpliesNode, VarNode, FnNode, LRNode
from unification import unify, subst

def select_hypothesis(screen):
    window = screen.win1
    pad = screen.pad1
    window.refresh()

    while True:
        c = screen.stdscr.getkey()
        if c == 'KEY_UP':
            pad.cursor_up()
            pad.refresh()
        elif c == 'KEY_DOWN':
            pad.cursor_down()
            pad.refresh()
        elif c == '\x1b': # ESC = cancel
            return -1
        elif c == '\n':
            return pad.scroll_line + pad.cursor_line

def modus_ponens(screen, tl):
    line1 = select_hypothesis(screen)
    if line1 == -1: # Cancelled
        return
    line2 = select_hypothesis(screen)
    if line2 == -1: # Cancelled
        return
    tlist1 = tl.tlist1
    tlist2 = tl.tlist2
    tree1 = tlist1.data[line1]
    tree2 = tlist1.data[line2]
    if not isinstance(tree2, ImpliesNode): # no implication after quantifiers
        return 
    qP1 = tree1
    qP2 = tree2.left
    unifies, assign = unify(qP1, qP2)
    if not unifies:
        return # does not unify, bogus selection
    n = tlist1.len()
    tlist1.data.append(substitute(tree2.right, assign))
    screen.pad1[n] = str(tlist1.data[n])# make substitutions
    # update windows
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def substitute(tree, assign):
   for (var, val) in assign:
       tree = subst(tree, var, val)
   return tree

def skolemize(screen, tl):
    tl0 = tl.tlist0.data # quantifier zone
    tl1 = tl.tlist1.data # hypotheses
    tl2 = tl.tlist2.data # targets
    deps = []
    sk = []
    qz = []
    mv = []
    if tl0:
        sq, deps, sk = skolemize_quantifiers(tl0[0], deps, sk)
        if sq:
            tl.tlist0.data[0] = sq
            screen.pad0[0] = str(tl.tlist0.data[0])
        else:
            del tl.tlist0.data[0]
            screen.pad0[0] = ''

    d = len(deps)
    s = len(sk)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()

    for i in range(0, len(tl1)):
        tl1[i] = skolemize_statement(tl1[i], deps, sk, qz, mv, False)
        rollback()
        screen.pad1[i] = str(tl1[i])
    for i in range(0, len(tl2)):
        tl2[i] = skolemize_statement(tl2[i], deps, sk, qz, mv, True)
        rollback()
        screen.pad2[i] = str(tl2[i])
    
    if qz:
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
        screen.pad0[0] = str(tl.tlist0.data[0])

    screen.focus.cursor_adjust()
    screen.pad0.refresh()
    screen.pad1.refresh()
    screen.pad2.refresh()
    screen.focus.refresh()

def skolemize_quantifiers(tree, deps, sk):
    if isinstance(tree, ExistsNode):
        sk.append((tree.var.name, len(deps)))
        deps.append(tree.var)
        return skolemize_quantifiers(tree.left, deps, sk)
    elif isinstance(tree, ForallNode):
        deps.append(tree.var)
        tree.left, deps, sk = skolemize_quantifiers(tree.left, deps, sk)
        return tree, deps, sk
    else:
        return tree, deps, sk

def skolemize_statement(tree, deps, sk, qz, mv, positive):
    d = len(deps)
    s = len(sk)

    def rollback():
        while len(deps) > d:
            deps.pop()
        while len(sk) > s:
            sk.pop()
 
    if isinstance(tree, ForallNode):
        if positive:
            deps.append(tree.var)
            qz.append(tree)
        else:
            mv.append(tree.var.name)
        tree.left = skolemize_statement(tree.left, deps, sk, qz, mv, positive)
        rollback()
        return tree.left
    elif isinstance(tree, ExistsNode):
        sk.append((tree.var.name, len(deps)))
        if positive:
            mv.append(tree.var.name)
        else:
            deps.append(tree.var)
            qz.append(ForallNode(tree.var, None))
        tree.left = skolemize_statement(tree.left, deps, sk, qz, mv, positive)
        rollback()
        return tree.left
    elif isinstance(tree, LRNode):
        tree.left = skolemize_statement(tree.left, deps, sk, qz, mv, positive)
        tree.right = skolemize_statement(tree.right, deps, sk, qz, mv, positive)
        rollback()
        return tree
    elif isinstance(tree, VarNode):
        is_meta = False
        if tree.name in mv:
            is_meta = True
            tree.is_metavar = True
        n = skolem_deps(tree.name, sk)
        if n == -1: # not a skolem variable
            return tree
        else:
            fn_args = [VarNode(deps[i].name, deps[i].type) \
                    for i in range(0, n)]
            fn = FnNode(tree.name, fn_args)
            fn.is_skolem = True
            if is_meta:
                fn.is_metavar = True
            return fn
    elif isinstance(tree, FnNode):
        for i in range(0, len(tree.args)):
            tree.args[i] = skolemize_statement(tree.args[i], deps, sk, qz, mv, positive)
            rollback()
        return tree
    else:
        return tree
        
def skolem_deps(name, sk):
    for (v, n) in sk:
        if v == name:
            return n
    return -1
