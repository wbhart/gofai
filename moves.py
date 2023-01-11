from navigation import navigate_up, navigate_down, delete_line, select_hypothesis
from interface.console import redraw, exit_console
from tree import tree_to_hypothesis, trees_match, trees_unify, tree_subst, tree_find_quantifier
from parser.ast import *
import copy

def apply_modus_ponens(stdscr, win1, win2, win3, pad1, pad2):
    main_pad = pad1
    main_window = win1
    line1 = select_hypothesis(stdscr, win1, pad1)
    if line1 == -1: # Cancelled
        return
    line2 = select_hypothesis(stdscr, win1, pad1)
    if line2 == -1: # Cancelled
        return
    tree1 = main_pad.data[line1][1]
    tree2 = main_pad.data[line2][1]
    # find the implication
    t = tree2
    last_q = None # last quantifier before implication
    while isinstance(t, ForallNode) or isinstance(t, ExistsNode):
        last_q = t
        t = t.expr
    while isinstance(t, ParenNode):
        last_q = t
        t = t.expr
    if not isinstance(t, ImpliesNode): # no implication after quantifiers
        return      
    # temporarily get rid of implication leaving only quantified right P
    impl = t # save implication to be replaced later
    if last_q == None: # there were no quantifiers
        qP2 = impl.left
    else:
        qP2 = tree2
        last_q.expr = impl.left
    # try to unify with left P
    qP1 = tree1
    unifies, assign = trees_unify(qP1, qP2)
    if not unifies: # doesn't unify, therefore bogus move
        if last_q != None:
            last_q.expr = impl # restore implication
        return
    # Find out which assigned variables are existentially vs universally quantified
    min_quant = []
    for (a, b) in assign:
        if isinstance(a, VarNode) and a.dbr > 0:
            p1 = tree_find_quantifier(qP1, a)
        else:
            p1 = a
        if isinstance(b, VarNode) and b.dbr > 0:
            p2 = tree_find_quantifier(qP2, b)
        else:
            p2 = b
        # exclude bad quantifier combinations
        if isinstance(p1, ExistsNode) and not isinstance(p2, ForallNode):
            return
        if not isinstance(p1, ForallNode) and not isinstance(p1, ExistsNode) and isinstance(p2, ExistsNode):
            return
        # Find the minimum quantifier for each pair
        if isinstance(p1, ForallNode) and isinstance(p2, ForallNode):
            min_quant.append((p2, ForallNode(VarNode(p1.var.name), None)))
        elif isinstance(p1, ExistsNode) or isinstance(p2, ExistsNode):
            min_quant.append((p2, ExistsNode(VarNode(p1.var.name), None)))
        elif isinstance(p2, ForallNode):
            min_quant.append((p2, p1))
        # else no substitution will be required
    # restore implication
    if last_q != None:
        last_q.expr = impl
    # temporarily remove implication and copy quantified Q
    impl = t # save implication to be replaced later
    if last_q == None: # there were no quantifiers
        qQ2 = impl.right
    else:
        qQ2 = tree2
        last_q.expr = impl.right
    Q = copy.deepcopy(qQ2)
    # restore implication
    if last_q != None:
        last_q.expr = impl
    # do substution
    newQ = tree_subst(Q, min_quant)
    tree_to_hypothesis(main_pad, main_pad.len(), newQ)
    redraw(main_window, main_pad)
    main_window.refresh()
              
def apply_delete_hypothesis(stdscr, win1, win2, win3, pad1, pad2):
    line = select_hypothesis(stdscr, win1, pad1)
    delete_line(main_window, main_pad, line)

def manual_moves(stdscr, win1, win2, win3, pad1, pad2):
    main_window = win1
    main_pad = pad1
    main_window.refresh()

    while True:
        c = stdscr.getkey()
        if c == '\t': # TAB = switch window focus (and associated pad)
            main_window = win2 if main_window == win1 else win1
            main_pad = pad2 if main_pad == pad1 else pad1
            main_window.refresh() # tell curses to update display (moves the cursor)
        elif c == 'd': # delete hypothesis
            apply_delete_hypothesis(stdscr, win1, win2, win3, pad1, pad2)
        elif c == '\x1b': # ESC = exit move mode
            break
        elif c == 'p': # Modus ponens
            apply_modus_ponens(stdscr, win1, win2, win3, pad1, pad2)
        
