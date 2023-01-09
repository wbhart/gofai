from navigation import navigate_up, navigate_down, delete_line
from interface.console import redraw
from tree import tree_to_hypothesis, trees_match
from parser.ast import *

def apply_modus_ponens(stdscr, win1, win2, win3, pad1, pad2):
    main_window = win1
    main_pad = pad1
    main_window.refresh()
    
    while True:
        c = stdscr.getkey()
        if c == 'KEY_UP':
            navigate_up(main_window, main_pad)
        elif c == 'KEY_DOWN':
            navigate_down(main_window, main_pad)
        elif c == '\x1b':
            break
        elif c == '\n':
            selected_tree = main_pad.data[main_pad.line][1]
            if isinstance(selected_tree, ImpliesNode): # make sure this is actually an implication
                prec = selected_tree.left # precedent of selected implication
                for h in range(0, main_pad.len()): # look through all hypotheses
                    s = main_pad.data[h][1] 
                    if trees_match(prec, s): # find a statement that matches precedent
                        tree_to_hypothesis(main_pad, main_pad.len(), selected_tree.right)
                        redraw(main_window, main_pad)
                        main_window.refresh()
                        return
                
def apply_delete_hypothesis(stdscr, win1, win2, win3, pad1, pad2):
    main_window = win1
    main_pad = pad1
    main_window.refresh()

    while True:
        c = stdscr.getkey()
        if c == 'KEY_UP':
            navigate_up(main_window, main_pad)
        elif c == 'KEY_DOWN':
            navigate_down(main_window, main_pad)
        elif c == '\x1b':
            break
        elif c == '\n':
            delete_line(main_window, main_pad, main_pad.line)
            break 

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
        
