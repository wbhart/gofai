import curses
import interface.console

def main():
    win1, win2 = interface.console.init_console()

    main_window = win1

    while True:
        c = main_window.getkey()
        if c == '\t':
            main_window = win2 if main_window == win1 else win1
            main_window.refresh()
        elif c == 'q':
            break
        else:
            continue

    interface.console.exit_console()

main()
