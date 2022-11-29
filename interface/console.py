import curses # console library
import curses.ascii # ascii class identification
from enum import Enum

def init_console():
    global stdscr
    stdscr = curses.initscr() # initialise curses, return object for entire screen
    curses.noecho() # turn off echoing of keys
    curses.cbreak() # don't wait for enter key upon input
    stdscr.keypad(True) # make it easier to read the keypad

    # compute width and height of windows
    width = curses.COLS
    height = curses.LINES
    win1_height = height//2
    win2_height = height//2

    # divide the screen into two windows half the height
    win1 = curses.newwin(win1_height, width, 0, 0)
    win2 = curses.newwin(win2_height, width, win1_height - 1, 0)
    win3 = curses.newwin(1, width, height - 1, 0)
 
    # print borders on the windows
    win1.border(curses.ACS_VLINE, curses.ACS_VLINE,
                curses.ACS_HLINE, curses.ACS_HLINE,
                curses.ACS_ULCORNER, curses.ACS_URCORNER,
                curses.ACS_LTEE, curses.ACS_RTEE)
    win2.border(curses.ACS_VLINE, curses.ACS_VLINE,
                curses.ACS_HLINE, curses.ACS_HLINE,
                curses.ACS_LTEE, curses.ACS_RTEE,
                curses.ACS_LLCORNER, curses.ACS_LRCORNER)

    # move the cursors inside the window boxes
    win1.move(1, 1)
    win2.move(1, 1)
    win3.move(0, 0)

    # redraw everything
    win3.refresh()
    win2.refresh()
    win1.refresh()

    return win1, win2, win3

def exit_console():
    curses.nocbreak() # wait for enter upon console input
    stdscr.keypad(False) # disable curses handling of keypad
    curses.echo() # echo characters to console
    curses.endwin() # return control of console

EditMode = Enum('EditMode', ['INSERT', 'REPLACE'])

def redraw_line(window, line, new_text, start, width, border=False):
    startx = 1 if border else 0
    line += (1 if border else 0)
    window.move(line, startx)
    for j in range(width):
        if start + j < len(new_text):
            window.addstr(new_text[start + j])
   
def process_char(window, new_text, i, cursor, width, mode, c):
    if mode == EditMode.REPLACE:
        new_text.insert(i, c)
        i += 1
        if cursor < width - 1:
            window.addstr(c)
            cursor += 1
        else:
            redraw_line(window, 0, new_text, i - width + 1, width - 1)
            window.addstr(0, width - 2, c)
        window.refresh()
    else: # INSERT
        new_text.insert(i, c)
        i += 1
        if cursor < width - 1:
            cursor += 1
        redraw_line(window, 0, new_text, i - cursor, width - 1)
        window.move(0, cursor)
        window.refresh()
    return i, cursor
       
def edit(window, start_text, i):
    window.refresh()
    mode = EditMode.INSERT
    new_text = list(start_text)
    (_, width) = window.getmaxyx() # get width of window display
    cursor = min(i, width - 1)
    redraw_line(window, 0, new_text, i - cursor, width - 1)
    window.move(0, cursor)
    window.refresh()

    while True:
        c = stdscr.getkey()
        if c == "KEY_RIGHT":
            if cursor < width - 1:
                if i < len(new_text):
                    cursor += 1
                    i += 1
                    window.move(0, cursor)
            else: # cursor = width - 1
                if i < len(new_text):
                    i += 1
                    redraw_line(window, 0, new_text, i - cursor, width - 1)
            window.refresh()
        elif c == "KEY_LEFT":
            if cursor > 0:
                cursor -= 1
                i -= 1
                window.move(0, cursor)
            else: # cursor = 0
                if i > 0:
                    i -= 1
                    redraw_line(window, 0, new_text, i - cursor, width - 1)
                    window.move(0, cursor)
            window.refresh()
        elif c == "KEY_BACKSPACE":
            if cursor == 0:
                if i > 0:
                    i -= 1
                    del new_text[i]
            else: # cursor > 0
                i -= 1
                del new_text[i]
                cursor -= 1
                redraw_line(window, 0, new_text, i - cursor, width - 1)
                if i - cursor + width - 1 > len(new_text):
                    window.addstr(0, cursor + len(new_text) - i, " ")    
                window.move(0, cursor)
                window.refresh()
        elif c == "KEY_DC": # delete key
            if i < len(new_text):
                del new_text[i]
                if cursor < width - 1:
                    redraw_line(window, 0, new_text, i - cursor, width - 1)
                    if i - cursor + width - 1 > len(new_text):
                        window.addstr(0, cursor + len(new_text) - i, " ")
                    window.move(0, cursor)
                    window.refresh()
        elif c == "KEY_IC": # insert key
            mode = EditMode.REPLACE if mode == EditMode.INSERT else EditMode.INSERT
        elif c == "\n": # enter key, KEY_ENTER is apparently unreliable
            window.clear()
            window.refresh()
            return ''.join(new_text)
        elif len(c) == 1: # and curses.ascii.isgraph(ord(c)):
            i, cursor = process_char(window, new_text, i, cursor, width, mode, c)
        else:
            continue

def clear_line(window, line, border=False):
    (_, width) = window.getmaxyx() # get width of window display
    start = 0 # starting x position
    if border:
        width -= 1
        start += 1
        line += 1
    window.addstr(line, start, ' '*(width - 1))
    window.move(line, start)
    window.refresh()

def report(window, string):
    clear_line(window, 0)
    window.addstr(0, 0, string)
    window.refresh()

def wait_for_key(key):
     while True:
        c = stdscr.getkey()
        if c == key:
            return

def redraw(window, pad):
    (height, width) = window.getmaxyx() # get width of window display
    width -= 2 # account for border
    height -= 2
    shift = pad.line - pad.cursor_line
    for i in range(0, height):
        clear_line(window, i, True)
        if i + shift < pad.len():
            redraw_line(window, i, pad.data[i + shift][0], pad.i - pad.cursor, width - 1, True)
    window.move(pad.cursor_line + 1, pad.cursor + 1)

class Pad:
    def __init__(self):
        self.data = []
        self.line = 0
        self.cursor = 0
        self.cursor_line = 0 # account for border
        self.i = 0

    def __setitem__(self, key, value):
        if key == len(self.data):
            self.data.append(value)
        else:
            self.data[key] = value

    def len(self):
        return len(self.data)

    def adjust(self):
        if self.line == len(self.data): # if we are on the final blank line
            self.i = 0
            self.cursor = 0
        else:
            data = self.data[self.line]
            line_length = len(data[0])
            if self.i > line_length: # character is beyond end of text
                self.i = line_length
                self.cursor = min(self.cursor, self.i)

