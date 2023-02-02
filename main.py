import curses # console library
import curses.ascii # ascii classification
from interface import Screen
from curses import wrapper
from editor import get_text
from tree import TreeList

from interface import iswide_char, nchars_to_chars

def main(stdscr):
    screen = Screen() # object representing console/windows
    tl = TreeList() # object representing lists of parsed statements

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
        elif c == 'm':
            screen.pad1.cursor_right(iswide_char(screen.pad1.pad[j][i]))
            screen.pad1.refresh()
            i += 1
        elif c == 'n':
            screen.pad1.cursor_left(iswide_char(screen.pad1.pad[j][i - 1]))
            screen.pad1.refresh()
            i -= 1
        elif c == 'l':
            screen.pad1.cursor_down()
            screen.pad1.refresh()
            j += 1
            i = screen.pad1.scroll_char + nchars_to_chars(screen.pad1.pad[j], \
                screen.pad1.scroll_char, screen.pad1.cursor_char)
        elif c == 'p':
            screen.pad1.cursor_up()
            screen.pad1.refresh()
            j -= 1
            i = screen.pad1.scroll_char + nchars_to_chars(screen.pad1.pad[j], \
                screen.pad1.scroll_char, screen.pad1.cursor_char)

    screen.exit()

wrapper(main) # curses wrapper handles exceptions
