from parser import statement, StatementVisitor
from enum import Enum
from interface import redraw_line
from parsimonious import exceptions

EditMode = Enum('EditMode', ['INSERT', 'REPLACE'])

def process_char(window, new_text, i, cursor, width, mode, c):
    """Deal with a character 'c' entered by the user, i.e. display it in the
    given window, scrolling if necessary, and insert it into the text string
    'new_text' at index 'i'. The cursor is assumed to be at x position
    'cursor' in the window, which is assumed to be without border. The edit
    mode REPLACE/INSERT is given by 'mode' and the width of the window is
    given by 'width'.
    """
    if mode == EditMode.REPLACE:
        new_text.insert(i, c) # insert new character in string 'new_text' at 'i'        i += 1
        if cursor < width - 1: # if not already at last character of line
            window.addstr(c) # replace the character at the given cursor x pos.
            cursor += 1
        else: # at last character of line in window
            # redraw entire line shifted one to the right in 'new_text'
            redraw_line(window, 0, new_text, i - width + 1, width)
            window.addstr(0, width - 2, c) # write last character of line
        window.refresh() # update display
    else: # INSERT
        new_text.insert(i, c) # insert character in string 'new_text'
        i += 1
        if cursor < width - 1: # move cursor if not at right
            cursor += 1
        # redraw entire line from 'new_text' with inserted character
        redraw_line(window, 0, new_text, i - cursor, width)
        window.move(0, cursor) # move cursor back to correct position
        window.refresh() # update display
    return i, cursor # return new index into text string and new cursor pos.

def edit(screen, start_text, i):
    """This is the main editor, in the status bar at the bottom of the screen.
    We start of with the given text, editing at index i in that text.
    """
    pad = screen.pad3
    window = pad.window
    stdscr = screen.stdscr
    window.refresh() # Gives the edit window the focus
    mode = EditMode.INSERT # Start in insert mode
    new_text = list(start_text) # New array for text (array of chars for now)
    width = pad.width # get width of window display
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
                    redraw_line(window, 0, new_text, i - cursor, width)
            window.refresh() # update display
        elif c == "KEY_LEFT": # left cursor was pressed
            if cursor > 0: # if not at left of window
                cursor -= 1 # move cursor pos. left
                i -= 1 # move left in text string
                window.move(0, cursor) # move to new cursor pos.
            else: # cursor = 0 (left of window)
                if i > 0: # if not at beginning of string
                    i -= 1 # dec. pos. in string and scroll window
                    redraw_line(window, 0, new_text, i - cursor, width)
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
                redraw_line(window, 0, new_text, i - cursor, width)
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
                    redraw_line(window, 0, new_text, i - cursor, width)
                    # blank dirty char. on right if not full width line
                    if i - cursor + width - 1 > len(new_text):
                        window.addstr(0, cursor + len(new_text) - i, " ")
                    window.move(0, cursor) # move cursor back to correct pos.
                    window.refresh() # update display
        elif c == "KEY_IC": # insert key
            # switch edit mode
            mode = EditMode.REPLACE if mode == EditMode.INSERT else \
                   EditMode.INSERT
        elif c == "\n": # enter key, KEY_ENTER is apparently unreliable
            window.clear() # clear edit window now that text is complete
            window.refresh() # update display
            return ''.join(new_text) # concat chars together into string
        elif len(c) == 1: # otherwise presumably character is printable
            # TODO: ignore nonprintable chars
            i, cursor = process_char(window, new_text, i, cursor, width, mode, c)
        else:
            continue

def get_text(screen, string):
    """Get a string from the user entered in the status bar, starting with the
       given string. The input is parsed into a tree by the input parser and
       any errors are noted by position so the user can correct them.
    """
    pad = screen.pad3
    index = 0 # index in current string to start editing
    while True:
        pad.clear_line(0) # clean line 0
        string = edit(screen, string, index) # get string from window
        try:
            ast = statement.parse(string) # parse input
            visitor = StatementVisitor()
            return visitor.visit(ast)
        except exceptions.IncompleteParseError as inst:
            index = inst.args[1]
            screen.dialog("Extra characters on line, starting at column "+str(index + 1)+". Press ENTER to continue")
        except exceptions.ParseError as inst:
            index = inst.pos
            screen.dialog("Error in statement starting at column "+str(index + 1)+". Press ENTER to continue")


