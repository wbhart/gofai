from interface.console import redraw, cursor_pos

def navigate_down(main_window, main_pad):
    if main_pad.line < main_pad.len(): # if we are not on the last line of data
        height, width = main_window.getmaxyx()
        if main_pad.cursor_line < height - 3: # if the cursor is not at the bottom of window
            main_pad.cursor_line += 1
        if main_pad.line + 1 < main_pad.len():
            line1 = main_pad.data[main_pad.line + 1][0]
            line2 = main_pad.data[main_pad.line][0]
            main_pad.i, diff = cursor_pos(line1, line2, main_pad.i)
            main_pad.cursor -= diff
        main_pad.line += 1 # move down one in the data
        main_pad.adjust() # new cursor line might be shorter, so adjust window
        redraw(main_window, main_pad) # redraw the window
        main_window.redrawwin()
        main_window.refresh() # tell curses it can now update display

def navigate_up(main_window, main_pad):
    if main_pad.line > 0: # if we are not on the first line of data
        if main_pad.cursor_line > 0: # if the cursor is not on first line of window
            main_pad.cursor_line -= 1
            if main_pad.line < main_pad.len():
                line1 = main_pad.data[main_pad.line - 1][0]
                line2 = main_pad.data[main_pad.line][0]
                main_pad.i, diff = cursor_pos(line1, line2, main_pad.i)
                main_pad.cursor -= diff
        main_pad.line -= 1 # move up one line in the data
        main_pad.adjust() # new cursor line might be shorter, so adjust window
        redraw(main_window, main_pad) # redraw the window
        main_window.redrawwin()
        main_window.refresh() # tell curses it can now update display

def select_hypothesis(stdscr, win1, pad1):
    main_window = win1
    main_pad = pad1
    main_window.refresh()

    while True:
        c = stdscr.getkey()
        if c == 'KEY_UP':
            navigate_up(main_window, main_pad)
        elif c == 'KEY_DOWN':
            navigate_down(main_window, main_pad)
        elif c == '\x1b': # ESC = cancel
            return -1
        elif c == '\n':
            return main_pad.line

def delete_line(main_window, main_pad, line):
    if line != main_pad.len(): # ensure we are not deleting blank line
        save_line = main_pad.line
        main_pad.line = line
        del main_pad.data[main_pad.line]
        main_pad.adjust() # after deleting line cursor may be on shorter line, so adjust window
        main_pad.line = save_line
        redraw(main_window, main_pad) # redraw the window
        main_window.refresh() # tell curses it can now update display
