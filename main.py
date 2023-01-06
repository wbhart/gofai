import curses
from curses import wrapper
from interface.console import Pad, clear_line, edit, exit_console, init_console, redraw, report, wait_for_key
from parser.input_parser import parse_hypothesis, HypothesisVisitor
from parser.debruijn import annotate_debruijn
from parsimonious import exceptions
from moves import manual_moves
from navigation import navigate_up, navigate_down
from tree import tree_to_hypothesis

# TODO : Add insert
# TODO : Allow cancelling of edit mode (ESC?)
# TODO : Allow pressing ESC to exit program ??
# TODO : Fix unicode bug when scrolling left/right and wide char straddles end of line
# TODO : Factor out a tab and left/right navigation in navigation.py and use in moves.py
# TODO : Add menu in status bar
# TODO : Add instructions in status bar when applying moves

def get_text(main_pad, main_window, win3):
    string = repr(main_pad.data[main_pad.line][1]) if main_pad.line != main_pad.len() else ""
    index = 0 # index in current string to start editing
    while True:
        clear_line(win3, 0)
        string = edit(win3, string, index) # get characters from edit window
        # main_window.refresh()
        try:
            ast = parse_hypothesis.parse(string) # parse input
            hv = HypothesisVisitor()
            output = hv.visit(ast)
            break
        except exceptions.IncompleteParseError as inst:
            index = inst.args[1]
            report(win3, "Extra characters on line, starting at column "+str(index + 1)+". Press ENTER to continue")
            wait_for_key("\n")
        except exceptions.ParseError as inst:
            index = inst.pos
            report(win3, "Error in statement starting at column "+str(index + 1)+". Press ENTER to continue")
            wait_for_key("\n")
    tree_to_hypothesis(main_pad, main_pad.line, output)

def main(stdscr):
    win1, win2, win3 = init_console()
    pad1 = Pad() # data that is in the windows (test + AST)
    pad2 = Pad()
    main_window = win1 # which window has focus
    main_pad = pad1

    while True:
        c = stdscr.getkey()
        if c == '\t': # TAB = switch window focus (and associated pad)
            main_window = win2 if main_window == win1 else win1
            main_pad = pad2 if main_pad == pad1 else pad1
            main_window.refresh() # tell curses to update display (moves the cursor)
        elif c == 'q': # q = quit
            break
        elif c == 'e': # e = edit
            get_text(main_pad, main_window, win3) # get text from user and parse
            main_pad.adjust() # line might now be shorter, so adjust window it is being inserted in
            redraw(main_window, main_pad) # redraw the window
            main_window.refresh() # tell curses it can now update display
        elif c == 'd': # d = delete line
            delete_line(main_window, main_pad, main_pad.line)
        elif c == 'm': # manual mode (allows the user to specify and apply moves)
            manual_moves(stdscr, win1, win2, win3, pad1, pad2)
            main_window.refresh()
        elif c == 'KEY_DOWN':
            navigate_down(main_window, main_pad)
        elif c == 'KEY_UP':
            navigate_up(main_window, main_pad)
        elif c == 'KEY_RIGHT':
            if main_pad.len() != main_pad.line: # check we are not on the blank line
                line = main_pad.data[main_pad.line][0]
                if main_pad.i < len(line): # if theres text to the right
                    extraw = 1 if ord(line[main_pad.i]) > 127 else 0 # account for wide chars
                    _, width = main_window.getmaxyx() # get width of window
                    main_pad.i += 1 # increment text pointer
                    if main_pad.cursor < width - 3: # if we aren't at the right of window
                        main_pad.cursor += 1 + extraw # increment cursor position and move there
                        main_window.move(main_pad.cursor_line + 1, main_pad.cursor + 1)
                        main_window.redrawwin()
                    else: # we are at the right of the window
                        redraw(main_window, main_pad) # redraw entire window (scroll)
                    main_window.refresh()
        elif c == 'KEY_LEFT':
            if main_pad.i > 0: # if we aren't at the beginning of the text
                line = main_pad.data[main_pad.line][0]
                extraw = 1 if main_pad.i > 1 and ord(line[main_pad.i - 2]) > 127 else 0 # take account of wide chars
                main_pad.i -= 1 # decrement text position
                if main_pad.cursor > 0: # if cursor isn't at beginning of line
                    main_pad.cursor -= 1 + extraw # decrement cursor posn. and move there
                    main_window.move(main_pad.cursor_line + 1, main_pad.cursor + 1)
                else: # we are at left of window
                    redraw(main_window, main_pad) # redraw entire window (scroll)
                main_window.refresh() # update display
        else:
            continue # ignore any other keys

    exit_console()

wrapper(main) # curses wrapper handles exceptions
