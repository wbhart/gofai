import curses
from curses import wrapper
from interface.console import Pad, clear_line, edit, exit_console, init_console, redraw, report, wait_for_key
from parser.input_parser import parse_hypothesis
from parsimonious import exceptions

def get_text(main_window, win3):
    string = ""
    index = 0 # index in current string to start editing
    while True:
        clear_line(win3, 0)
        string = edit(win3, string, index) # get characters from edit window
        # main_window.refresh()
        try:
            ast = parse_hypothesis.parse(string) # parse input
            break
        except exceptions.IncompleteParseError as inst:
            index = inst.args[1]
            report(win3, "Extra characters on line, starting at column "+str(index + 1)+". Press ENTER to continue")
            wait_for_key("\n")
        except exceptions.ParseError as inst:
            index = inst.pos
            report(win3, "Error in statement starting at column "+str(index + 1)+". Press ENTER to continue")
            wait_for_key("\n")
    return string, ast

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
            main_window.refresh()
        elif c == 'q': # q = quit
            break
        elif c == 'e': # e = edit
            main_pad[main_pad.line] = get_text(main_window, win3)
            main_pad.adjust()
            redraw(main_window, main_pad)
            main_window.refresh()
        elif c == 'KEY_DOWN':
            if main_pad.line < main_pad.len():
                height, width = main_window.getmaxyx()
                if main_pad.cursor_line < height - 3:
                    main_pad.cursor_line += 1
                main_pad.line += 1
                main_pad.adjust()
                redraw(main_window, main_pad)
                main_window.refresh()
        else:
            continue

    exit_console()

wrapper(main) # curses wrapper handles exceptions
