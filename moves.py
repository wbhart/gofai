from navigation import navigate_up, navigate_down, delete_line, select_hypothesis
from interface.console import redraw
from tree import tree_to_hypothesis, trees_match, tree_is_Px
from parser.ast import *

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
    if isinstance(tree1, ImpliesNode): # check if first selection is an implication 
        if trees_match(tree1.left, tree2): # P, P => Q case
            tree_to_hypothesis(main_pad, main_pad.len(), tree1.right)
            redraw(main_window, main_pad)
            main_window.refresh()
        elif isinstance(tree2, ForallNode): # \forall P(x), P(a) => Q
            matched, _, _ = tree_is_Px(tree1.left, tree2)
            if matched:
                tree_to_hypothesis(main_pad, main_pad.len(), tree1.right)
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
        
