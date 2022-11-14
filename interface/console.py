import curses # console library

def init_console():
    global stdscr
    stdscr = curses.initscr() # initialise curses, return object for entire screen
    curses.noecho() # turn off echoing of keys
    curses.cbreak() # don't wait for enter key upon input
    stdscr.keypad(True) # make it easier to read the keypad

    width = curses.COLS
    height = curses.LINES
    win1_height = (height - 1)//2
    win2_height = (height - 1)//2

    # divide the screen into two windows less than half the height
    win1 = curses.newwin(win1_height, width, 0, 0)
    win2 = curses.newwin(win2_height, width, win1_height, 0)
    
    win1.box()
    win2.box()

    win1.move(1, 1)
    win2.move(1, 1)

    win2.refresh()
    win1.refresh()

    # draw lines to separate windows
    #win1.addstr(win1_height - 1, 0, "="*(width-1))
    #win1.insstr(win1_height - 1, width - 1, "=") # last character can't be written directly!!

    return win1, win2

def exit_console():
    curses.nocbreak() # wait for enter upon console input
    stdscr.keypad(False) # disable curses handling of keypad
    curses.echo() # echo characters to console
    curses.endwin() # return control of console
