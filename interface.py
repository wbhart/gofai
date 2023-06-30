import curses # console library
import curses.ascii # ascii classification
from enum import Enum
from curses import wrapper

EditMode = Enum('EditMode', ['INSERT', 'REPLACE'])

def iswide_char(c):
    if c == '\u22A4' or c == '\u2115' or c == '\u2124' or \
       c == '\u2102' or c == '\u211a' or c == '\u211d' or c == '\u0307' or \
       c == '\u2205' or c == '\u00ac' or (ord(c) >= 8320 and ord(c) <= 8329):
        return False
    return ord(c) > 127

def redraw_line_with_reverse(window, line, string, i, width, rev1, rev2, border=False):
    """Write the given unicode string starting at character i to the given
       window of the given width, adjusting for the border if it exists.
       Characters in the range [rev1, rev2) will be reversed
    """
    start = 1 if border else 0
    # clear line
    window.move(line + start, start)
    for j in range(0, width - 2*start - 1):
        window.addch(' ')
    # draw new line
    j = 0
    k = 0
    window.move(line + start, start)
    while j < width - 2*start - 1:
        if i + k < len(string):
            c = string[i + k]
            if i + k >= rev1 and i + k < rev2:
                window.addch(c, curses.A_REVERSE)
            else:
                window.addch(c)
            j += 2 if iswide_char(c) else 1
        else:
            window.addch(' ')
            j += 1
        k += 1

def redraw_line(window, line, string, i, width, border=False):
    redraw_line_with_reverse(window, line, string, i, width, 0, 0, border)

def adjust_nchars(string, scroll_chars, nchars):
    """Given a unicode string which we have scrolled the given number of chars
       return (j, extra) where j is the number of chars past the scroll to
       reach the given nchar. If we are 1 nchar short, extra will be set to 1,
       otherwise 0.
    """
    k = 0
    j = 0
    while j < nchars - 1 and scroll_chars + k < len(string):
        c = string[scroll_chars + k]
        j += 2 if iswide_char(c) else 1
        k += 1
    if scroll_chars + k < len(string):
        c = string[scroll_chars + k]
        if not iswide_char(c) and j < nchars:
            j += 1
    return j

def nchars_to_chars(string, scroll_chars, nchars):
    """Return the number of chars past scroll_chars to achieve the given number
       of nchars.
    """
    k = 0
    j = 0
    while j < nchars:
        c = string[scroll_chars + k]
        j += 2 if iswide_char(c) else 1
        k += 1
    return k

class Pad:
    def __init__(self, window, lines, y, x, height, width, border=False):
        """Initialise a pad of the given number of lines for display within a
           window starting at absolute screen position (y, x). When the pad
           scrolls left/right it moves by 1 full char (narrow or wide) at a
           time, for every line. When the cursor moves, it only moves by 1
           narrow char (nchar) at a time.
        """
        self.scroll_line = 0 # which line of the pad is at the upper left of window
        self.scroll_char = 0 # how many chars is the pad scrolled from the left
        self.cursor_line = 0 # which line of the window is the cursor on
        self.cursor_char = 0 # which nchar position is the cursor on
        self.rev1 = 0        # start of reverse attribute of string
        self.rev2 = 0        # stop of reverse attribute of string
        
        self.save = [0, 0, 0, 0] # to save and restore state

        self.window = window
        self.pad = ['' for i in range(0, lines)] # blank pad with given number of lines
        self.x = x # absolute screen position of upper left corner of pad
        self.y = y
        self.height = height # height of visible portion of pad on screen
        self.width = width # width of visible portion of pad on screen

        self.lines = lines # number of lines allocated in pad
        self.border = border # whether the pad window has a border

        self.refresh()

    def save_state(self):
        self.save[0] = self.scroll_line
        self.save[1] = self.scroll_char
        self.save[2] = self.cursor_line
        self.save[3] = self.cursor_char

    def restore_state(self):
        self.scroll_line = self.save[0]
        self.scroll_char = self.save[1]
        self.cursor_line = self.save[2]
        self.cursor_char = self.save[3]

    def inch(self, y, x):
        return self.pad[y][x]

    def move_right(self, iswide=False):
        """Move the cursor right one char and scroll the window if necessary.
           The function needs to be supplied with a parameter to say whether
           the character under the cursor is wide or not.
        """
        start = 1 if self.border else 0
        if self.cursor_char < self.width - 2*start - 2: # not at right of window
            self.cursor_char += 2 if iswide else 1 # just move the cursor
        else:
            c = self.inch(self.scroll_line + self.cursor_line, self.scroll_char)
            self.scroll_char += 1
            if iswide_char(c): # line will move two nchars
                if not iswide: # next char is only one nchar
                    self.cursor_char -= 1
            else: # line would only move 1 nchar
                if iswide: # next char is two nchars
                    self.cursor_char += 1
                    if self.cursor_char >= self.width - 2*start - 3: # we need to move one more char
                        c = self.inch(self.scroll_line + self.cursor_line, self.scroll_char)
                        self.scroll_char += 1
                        self.cursor_char -= 2 if iswide_char(c) else 1

    def move_left(self, iswide=False):
        """Move the cursor left one char and scroll the window if necessary.
           The function needs to know if the character to the left is wide.
        """
        if self.cursor_char > 0: # not at left of window
            self.cursor_char -= 2 if iswide else 1 # just move the cursor
        else:
            self.scroll_char -= 1

    def cursor_adjust(self):
        self.cursor_char = adjust_nchars(self.pad[self.scroll_line + self.cursor_line], \
                            self.scroll_char, self.cursor_char)

    def cursor_left(self):
        """Move the cursor left one char and scroll the window if necessary.
        """
        line = self.scroll_line + self.cursor_line
        string = self.pad[line]
        i = self.scroll_char + nchars_to_chars(string, \
                self.scroll_char, self.cursor_char) # current pos. within string
        if i > 0:
            iswide = iswide_char(string[i - 1])
            self.move_left(iswide)

    def cursor_right(self):
        """Move the cursor left one char and scroll the window if necessary.
        """
        line = self.scroll_line + self.cursor_line
        string = self.pad[line]
        i = self.scroll_char + nchars_to_chars(string, \
                self.scroll_char, self.cursor_char) # current pos. within string
        if i < len(string):
            iswide = iswide_char(string[i])
            self.move_right(iswide)

    def cursor_down(self):
        start = 1 if self.border else 0
        if self.cursor_line < self.height - 1:
            # just move the cursor
            self.cursor_line += 1
        else:
            self.scroll_line += 1
        self.cursor_adjust()
 
    def cursor_up(self):
        start = 1 if self.border else 0
        if self.cursor_line > 0:
            # just move the cursor
            self.cursor_line -= 1
        else:
            self.scroll_line -= 1
        self.cursor_adjust()

    def move(self, y, x):
        """Move cursor to position (y, x) in pad (assuming it is in range).
        """
        self.cursor_line = y - self.scroll_line
        self.cursor_char = x - self.scroll_char

    def clear_line(self, line):
        """Clear the line with index 'line' in the given window (index starting
        at 0) avoiding the border if there is one (specified by 'border=True').
        """
        width = self.width # get width of window display
        start = 0 # starting x position
        if self.border: # adjust starting pos., width and line index for border
            width -= 1
            start += 1
            line += 1
        self.window.addstr(line, start, ' '*(width - 1))
    
    def refresh(self):
        """Redraw the pad in position on screen. Due to bugs in python curses
           when working with unicode on WSL, this needs to be done by hand.
        """
        for y in range(0, self.height):
            line = y + self.scroll_line
            if line < len(self.pad):
                if line == self.cursor_line + self.scroll_line:
                    redraw_line_with_reverse(self.window, y, self.pad[line], self.scroll_char, self.width, self.rev1, self.rev2, border=self.border)
                else:
                    redraw_line(self.window, y, self.pad[line], self.scroll_char, self.width, border=self.border)

        start = 1 if self.border else 0
        self.window.move(self.cursor_line + start, self.cursor_char + start)
        self.window.refresh()
        self.window.redrawwin()
        self.window.refresh()
        self.window.redrawwin()
        self.window.refresh()

    def __setitem__(self, key, value):
        """Overload array notation so lines can be added.
        """
        self.pad[key] = value

class Screen:
    def __init__(self):
        """Initialise the console for use, including drawing the windows on the
           screen and initialising the corresponding pads. The screen includes
           a quantifier zone, a hypothesis window, a target window and a status
           bar. The first three will have borders.
        """
        self.stdscr = curses.initscr() # initialise curses, return object for entire screen
        curses.noecho() # turn off echoing of keys
        curses.cbreak() # don't wait for enter key upon input
        self.stdscr.keypad(True) # make it easier to read the keypad
        
        # compute window heights, leaving room for the quantifier zone and status bar
        self.win1_height = (curses.LINES - 2)//2
        self.win2_height = curses.LINES - self.win1_height - 2

        # divide the screen into three bordered windows and space for status bar
        self.win0 = curses.newwin(3, curses.COLS, 0, 0)
        self.win1 = curses.newwin(self.win1_height, curses.COLS, 2, 0)
        self.win2 = curses.newwin(self.win2_height, curses.COLS, self.win1_height + 1, 0)
        self.win3 = curses.newwin(1, curses.COLS, curses.LINES - 1, 0)

        # print borders on the windows
        self.win0.border(curses.ACS_VLINE, curses.ACS_VLINE,
                    curses.ACS_HLINE, curses.ACS_HLINE,
                    curses.ACS_ULCORNER, curses.ACS_URCORNER,
                    curses.ACS_LTEE, curses.ACS_RTEE)
        self.win1.border(curses.ACS_VLINE, curses.ACS_VLINE,
                    curses.ACS_HLINE, curses.ACS_HLINE,
                    curses.ACS_LTEE, curses.ACS_RTEE,
                    curses.ACS_LTEE, curses.ACS_RTEE)
        self.win2.border(curses.ACS_VLINE, curses.ACS_VLINE,
                    curses.ACS_HLINE, curses.ACS_HLINE,
                    curses.ACS_LTEE, curses.ACS_RTEE,
                    curses.ACS_LLCORNER, curses.ACS_LRCORNER)

        # draw border windows
        self.win0.refresh()
        self.win1.refresh()
        self.win2.refresh()

        # initialise pads with plenty of lines
        self.pad0 = Pad(self.win0, 1, 1, 1, 1, curses.COLS, border=True)
        self.pad1 = Pad(self.win1, 100, 3, 1, self.win1_height - 2, curses.COLS, border=True)
        self.pad2 = Pad(self.win2, 100, self.win1_height + 2, 1, self.win2_height - 2, curses.COLS, border=True)
        self.pad3 = Pad(self.win3, 1, curses.LINES - 1, 0, 1, curses.COLS)

        # pad with current focus
        self.focus = self.pad0

        # update screen
        self.pad3.refresh()
        self.pad2.refresh()
        self.pad1.refresh()
        self.pad0.refresh()

        self.edit_text = [] # text entered at the edit/status bar as chars

    def save_state(self):
        self.pad1.save_state()
        self.pad2.save_state()

    def restore_state(self):
        self.pad1.restore_state()
        self.pad2.restore_state()
        
    def exit(self):
        """Return control of the console from curses back to Python,
        """
        curses.nocbreak() # wait for enter upon console input
        self.stdscr.keypad(False) # disable curses handling of keypad
        curses.echo() # echo characters to console
        curses.endwin() # return control of console

    def wait_key(self, key):
         """Wait for the given key to be pressed.
         """
         while True:
             c = self.stdscr.getkey()
             if c == key:
                  return

    def status(self, string):
        """Print the specified message in the status bar of the window.
        """
        pad = self.pad3
        window = pad.window
        pad.clear_line(0) # clear the entire line
        window.addstr(0, 0, string[0:pad.width-1]) # output string
        window.refresh() # update display

    def dialog(self, string):
        """Print the given status message and wait for a key to be pressed.
        """
        self.status(string)
        self.wait_key("\n")
        self.status("")

    def switch_window(self):
        """Switch focus to next pad (0-2).
        """
        if self.focus == self.pad0:
            self.focus = self.pad1
        elif self.focus == self.pad1:
            self.focus = self.pad2
        elif self.focus == self.pad2:
            self.focus = self.pad0
        self.focus.refresh()

    def process_char(self, i, mode, c):
        """Deal with a character 'c' entered at the status bar, scrolling if
           necessary, and insert it into the text string at index 'i'. The edit
           mode REPLACE/INSERT is given by 'mode'.
        """
        pad = self.pad3
        window = pad.window
        edit_text = self.edit_text
        if mode == EditMode.REPLACE:
            if i == len(edit_text):
                edit_text.append(c)
            else:
                edit_text[i] = c # overwrite char at index 'i'
        else: # INSERT
            edit_text.insert(i, c) # insert character in string 'edit_text'
        pad.pad[0] = ''.join(edit_text)
        pad.cursor_right()
        pad.refresh() # update display
