import curses
from curses import wrapper
from interface.console import init_console, exit_console, edit, report, clear_line, wait_for_key
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

def main(stdscr):
    win1, win2, win3 = init_console()

    main_window = win1

    while True:
        c = main_window.getkey()
        if c == '\t': # TAB = switch windows
            main_window = win2 if main_window == win1 else win1
            main_window.refresh()
        elif c == 'q': # q = quit
            break
        elif c == 'e': # e = edit
            get_text(main_window, win3)
            main_window.refresh()
        else:
            continue

    exit_console()

wrapper(main) # curses wrapper handles exceptions
