import curses
from curses import wrapper
from interface.console import init_console, exit_console, edit
from parser.input_parser import parse_hypothesis

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
            text_chars = edit(win3, []) # get characters from edit window
            text = ''.join(text_chars) # join the list of chars together to make a string
            main_window.refresh()
            ast = parse_hypothesis.parse(text) # parse input
        else:
            continue

    exit_console()

wrapper(main) # curses wrapper handles exceptions
