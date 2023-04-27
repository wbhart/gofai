from parser import statement, to_ast
from interface import EditMode

def edit(screen, start_text, i):
    """This is the main editor, in the status bar at the bottom of the screen.
    We start of with the given text, editing at index i in that text.
    """
    pad = screen.pad3
    window = pad.window
    stdscr = screen.stdscr
    mode = EditMode.INSERT # Start in insert mode
    screen.edit_text = list(start_text) # New array of chars for text
    pad.pad[0] = start_text
    pad.cursor_char = min(i, pad.width - 1) # min(text index, window right)
    pad.scroll_char = i - pad.cursor_char
    pad.refresh()

    while True:
        c = stdscr.getkey() # get a key from terminal
        if c == "KEY_RIGHT": # right cursor was pressed
            if i < len(screen.edit_text):
                pad.cursor_right()
                pad.refresh()
                i += 1
        elif c == "KEY_LEFT": # left cursor was pressed
            if i > 0:
                pad.cursor_left()
                pad.refresh()
                i -= 1
        elif c == "KEY_BACKSPACE": # backspace key pressed
            if pad.cursor_char == 0: # if at left of window
                if i > 0: # if not at beginning of text
                    i -= 1 # decrement pos. in text and delete character there
                    del screen.edit_text[i]
                    pad.pad[0] = ''.join(screen.edit_text)
            else: # cursor > 0 (not left of window)
                i -= 1 # dec. pos. in text and delete character there
                del screen.edit_text[i]
                pad.cursor_left()
                pad.pad[0] = ''.join(screen.edit_text)
                pad.refresh() # update display
        elif c == "KEY_DC": # delete key pressed
            if i < len(screen.edit_text): # if not beyond end of text string
                del screen.edit_text[i] # delete character at curr. str. pos
                pad.pad[0] = ''.join(screen.edit_text)
                if pad.cursor_char < pad.width - 1: # if cursor not at right
                    pad.refresh() # update display
        elif c == "KEY_IC": # insert key
            # switch edit mode
            mode = EditMode.REPLACE if mode == EditMode.INSERT else \
                   EditMode.INSERT
        elif c == "\n": # enter key, KEY_ENTER is apparently unreliable
            window.clear() # clear edit window now that text is complete
            window.refresh() # update display
            return ''.join(screen.edit_text) # concat chars together into string
        elif len(c) == 1: # otherwise presumably character is printable
            # TODO: ignore nonprintable chars
            screen.process_char(i, mode, c)
            i += 1
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
        return to_ast(screen, string)


