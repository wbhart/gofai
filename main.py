import curses # console library
import curses.ascii # ascii classification
from interface import Screen
from curses import wrapper
from editor import get_text

from interface import iswide_char, nchars_to_chars

def main(stdscr):
    screen = Screen()

    while True:
        c = stdscr.getkey()
        if c == '\t': # TAB = switch window focus (and associated pad)
            screen.switch_window()
        elif c == 'q': # q = quit
            break
        elif c == 'e': # e = editi
            get_text(screen, "") # get text from user and parse
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
