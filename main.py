import curses # console library
import curses.ascii # ascii classification
from interface import Screen, iswide_char, nchars_to_chars
from curses import wrapper
from editor import get_text
from tree import TreeList
from automation import AutoDict, automate
from moves import skolemize, modus_ponens

def main(stdscr):
    screen = Screen() # object representing console/windows
    tl = TreeList() # object representing lists of parsed statements
    ad = AutoDict() # get initial automation dictionary containing basic axioms

    while True:
        c = stdscr.getkey()
        if c == '\t': # TAB = switch window focus (and associated pad)
            screen.switch_window()
            tl.switch_list()
        elif c == 'q': # q = quit
            break
        elif c == 'e': # e = edit
            line = tl.focus.line
            data = '' if line == tl.focus.len() else repr(tl.focus.data[line])
            tree = get_text(screen, data) # parse text from user
            tl.focus[line] = tree # insert tree in treelist
            screen.focus[line] = str(tree) # insert unicode string into pad
            screen.focus.refresh()
        elif c == 'a': # a = automate
            automate(screen, tl, ad)
        elif c == 's': # skolemize
            skolemize(screen, tl)
        elif c == 'p': # modus ponens
            modus_ponens(screen, tl)
        elif c == 'KEY_RIGHT':
            pad = screen.focus
            pad.cursor_right()
            pad.refresh()
        elif c == 'KEY_LEFT':
            pad = screen.focus
            pad.cursor_left()
            pad.refresh()
        elif c == 'KEY_DOWN':
            pad = screen.focus
            if pad != screen.pad0 and tl.focus.line != tl.focus.len():
                pad.cursor_down()
                pad.refresh()
                tl.focus.line += 1
        elif c == 'KEY_UP':
            pad = screen.focus
            if pad != screen.pad0 and tl.focus.line != 0:
                pad.cursor_up()
                pad.refresh()
                tl.focus.line -= 1

    screen.exit()

wrapper(main) # curses wrapper handles exceptions
