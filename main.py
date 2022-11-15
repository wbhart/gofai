import curses
from curses import wrapper
import interface.console

def main(stdscr):
    win1, win2, win3 = interface.console.init_console()

    main_window = win1

    while True:
        c = main_window.getkey()
        if c == '\t': # TAB = switch windows
            main_window = win2 if main_window == win1 else win1
            main_window.refresh()
        elif c == 'q': # q = quit
            break
        elif c == 'e': # e = edit
            interface.console.edit(win3, [], 1000)
            main_window.refresh()
        else:
            continue

    interface.console.exit_console()

wrapper(main) # curses wrapper handles exceptions
