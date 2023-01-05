import curses # console library
import curses.ascii # ascii class identification
from enum import Enum

def init_console():
    """Initialise the windows for use. Divides the screen roughly in half
    with a status line at the bottom. Windows have a border.
    """
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
    """Return control of the console from curses back to Python"""
    curses.nocbreak() # wait for enter upon console input
    stdscr.keypad(False) # disable curses handling of keypad
    curses.echo() # echo characters to console
    curses.endwin() # return control of console

EditMode = Enum('EditMode', ['INSERT', 'REPLACE'])

def redraw_line(window, line, new_text, start, width, border=False):
    """Redraw the line with index 'line' in a given window based on the array
    of text 'new_text' starting at index 'start' of the array. Adjustments are
    made to avoid the border if there is one, specified by 'border=True'. The
    window is taken to have width given by 'width' (after accounting for the
    border, which caller must do. Note the existing line is not cleared by
    this function so if width is less than the width of the display area then
    additional characters may be left behind."""
    startx = 1 if border else 0 # starting x position on line (border aware)
    line += (1 if border else 0) # line in the window (border aware)
    window.move(line, startx) # move cursor to start position
    for j in range(width):
        if start + j < len(new_text): # check there's text for that posn.
            window.addstr(new_text[start + j]) # write the text if so
   
def process_char(window, new_text, i, cursor, width, mode, c):
    """Deal with a character 'c' entered by the user, i.e. display it in the
    given window, scrolling if necessary, and insert it into the text string
    'new_text' at index 'i'. The cursor is assumed to be at x position
    'cursor' in the window, which is assumed to be without border. The edit
    mode REPLACE/INSERT is given by 'mode' and the width of the window is
    given by 'width'.
    """
    if mode == EditMode.REPLACE:
        new_text.insert(i, c) # insert new character in string 'new_text' at 'i'
        i += 1
        if cursor < width - 1: # if not already at last character of line
            window.addstr(c) # replace the character at the given cursor x pos.
            cursor += 1
        else: # at last character of line in window
            # redraw entire line shifted one to the right in 'new_text'
            redraw_line(window, 0, new_text, i - width + 1, width - 1)
            window.addstr(0, width - 2, c) # write last character of line
        window.refresh() # update display
    else: # INSERT
        new_text.insert(i, c) # insert character in string 'new_text'
        i += 1
        if cursor < width - 1: # move cursor if not at right
            cursor += 1
        # redraw entire line from 'new_text' with inserted character
        redraw_line(window, 0, new_text, i - cursor, width - 1)
        window.move(0, cursor) # move cursor back to correct position
        window.refresh() # update display
    return i, cursor # return new index into text string and new cursor pos.
       
def edit(window, start_text, i):
    """This is the main editor, in the status bar at the bottom of the screen,
    i.e. window3. We start of with the given text, editing at index i in that
    text.
    """
    window.refresh() # Gives the edit window the focus
    mode = EditMode.INSERT # Start in insert mode
    new_text = list(start_text) # New array for text (array of chars for now)
    (_, width) = window.getmaxyx() # get width of window display
    cursor = min(i, width - 1) # set cursor to min(text index i or line right)
    redraw_line(window, 0, new_text, i - cursor, width - 1) # display text
    window.move(0, cursor) # move cursor to the right place
    window.refresh() # update display

    while True:
        c = stdscr.getkey() # get a key from terminal
        if c == "KEY_RIGHT": # right cursor was pressed
            if cursor < width - 1: # if we are not at right of window
                if i < len(new_text): # if not at end of text
                    cursor += 1 # increment cursor pos.
                    i += 1 # increment text pos.
                    window.move(0, cursor) # move to new cursor pos.
            else: # cursor = width - 1 (right of window)
                if i < len(new_text): # if not at end of text
                    i += 1 # increment text position only and scroll window
                    redraw_line(window, 0, new_text, i - cursor, width - 1)
            window.refresh() # update display
        elif c == "KEY_LEFT": # left cursor was pressed
            if cursor > 0: # if not at left of window
                cursor -= 1 # move cursor pos. left
                i -= 1 # move left in text string
                window.move(0, cursor) # move to new cursor pos.
            else: # cursor = 0 (left of window)
                if i > 0: # if not at beginning of string
                    i -= 1 # dec. pos. in string and scroll window
                    redraw_line(window, 0, new_text, i - cursor, width - 1)
                    window.move(0, cursor) # move cursor back to left of window
            window.refresh() # update display
        elif c == "KEY_BACKSPACE": # backspace key pressed
            if cursor == 0: # if at left of window
                if i > 0: # if not at beginning of text
                    i -= 1 # decrement pos. in text and delete character there
                    del new_text[i]
            else: # cursor > 0 (not left of window)
                i -= 1 # dec. pos. in text and delete character there
                del new_text[i]
                cursor -= 1
                # redraw entire line from string with deleted char
                redraw_line(window, 0, new_text, i - cursor, width - 1)
                # blank dirty char on line if line less than full width
                if i - cursor + width - 1 > len(new_text):
                    window.addstr(0, cursor + len(new_text) - i, " ")    
                window.move(0, cursor) # move cursor back to correct pos.
                window.refresh() # update display
        elif c == "KEY_DC": # delete key pressed
            if i < len(new_text): # if not beyond end of text string
                del new_text[i] # delete character at curr. str. pos.
                if cursor < width - 1: # if cursor not at right
                    # redraw entire line with deleted char.
                    redraw_line(window, 0, new_text, i - cursor, width - 1)
                    # blank dirty char. on right if not full width line
                    if i - cursor + width - 1 > len(new_text):
                        window.addstr(0, cursor + len(new_text) - i, " ")
                    window.move(0, cursor) # move cursor back to correct pos.
                    window.refresh() # update display
        elif c == "KEY_IC": # insert key
            # switch edit mode
            mode = EditMode.REPLACE if mode == EditMode.INSERT else EditMode.INSERT
        elif c == "\n": # enter key, KEY_ENTER is apparently unreliable
            window.clear() # clear edit window now that text is complete
            window.refresh() # update display
            return ''.join(new_text) # concat chars together into string
        elif len(c) == 1: # otherwise presumably character is printable
            # TODO: ignore nonprintable chars
            i, cursor = process_char(window, new_text, i, cursor, width, mode, c)
        else:
            continue

def clear_line(window, line, border=False):
    """Clear the line with index 'line' in the given window (index starting at
    0) avoiding the border if there is one (specified by 'border=True')..
    """
    (_, width) = window.getmaxyx() # get width of window display
    start = 0 # starting x position
    if border: # adjust starting pos., width and line index for border
        width -= 1
        start += 1
        line += 1
    window.addstr(line, start, ' '*(width - 1))
    window.move(line, start) # move cursor to start of line
    # TODO: move seems orthogonal, perhaps make caller do this and refresh?
    window.refresh() # update display

def report(window, string):
    """Print the error message with given 'string' in given 'window'.
    """
    clear_line(window, 0) # clear the entire line
    window.addstr(0, 0, string) # output string
    window.refresh() # update display

def wait_for_key(key):
     """Wait for the given key to be pressed.
     """
     while True:
        c = stdscr.getkey()
        if c == key:
            return

def adjusted_i(line, i, cursor):
    """Adjust i - cursor for wide characters in line"""
    while cursor > 0:
        # TODO: this is not correct if wide char straddles start of line
        cursor -= (2 if ord(line[i - 1]) > 127 else 1)
        i -= 1
    return i

def redraw(window, pad):
    """Fill the given window with lines of text from the given Pad structure.
    Details about cursor position and window position within text are in the
    Pad structure. Assumes window has a border."""
    (height, width) = window.getmaxyx() # get height/width of window display
    width -= 2 # account for border
    height -= 2
    # compute line in pad corresponding to first line of window
    shift = pad.line - pad.cursor_line
    for i in range(0, height): # we'll display 'height' lines from pad
        clear_line(window, i, True) # clear entire line before writing it
        if i + shift < pad.len(): # if there's a text line for this window line
            # write the line to window shifting for cursor and text x position
            line = pad.data[i + shift][0]
            redraw_line(window, i, line, adjusted_i(line, pad.i, pad.cursor), width - 1, True)
    window.move(pad.cursor_line + 1, pad.cursor + 1) # move cursor back to correct pos.
    window.redrawwin() # work around a bug in curses where lines are not properly cleared

class Pad:
    """Structure to contain parsed text strings for a window. Each line
    consists of a text string and AST pair.
    """
    def __init__(self):
        self.data = [] # line text/AST pair array
        self.line = 0 # which line of text does cursor line correspond to
        self.cursor = 0 # which cursor x position in window are we at
        self.cursor_line = 0 # which window line is cursor on
        self.i = 0 # which text x char. pos. does cursor pos. correspond to

    def __setitem__(self, key, value):
        """Overload array notation for pad so lines can be added.
        """
        if key == len(self.data): # normal array notation doesn't allow append
            self.data.append(value)
        else:
            self.data[key] = value

    def len(self):
        """Return number of lines in pad.
        """
        return len(self.data)

    def adjust(self):
        """Adjust internal position data of pad assuming current line.
        """
        if self.line == len(self.data): # if we are on the final blank line
            self.i = 0 # line has len 0 so shift text/cursor pos to left
            self.cursor = 0
        else: # not on final blank line
            data = self.data[self.line]
            line_length = len(data[0])
            if self.i > line_length: # character is beyond end of text
                shift = self.i - self.cursor
                self.cursor = min(self.cursor, max(line_length - shift, 0))
                self.i = line_length # adjust to end of text in current line

