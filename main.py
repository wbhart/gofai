import curses # console library
import curses.ascii # ascii classification
from interface import Screen, iswide_char, nchars_to_chars
from curses import wrapper
from editor import get_text, edit
from tree import TreeList
from automation import AutoDict, automate
from moves import cleanup, modus_ponens, modus_tollens, library_export, \
     library_import, clear_tableau, equality, targets_proved, TargetNode, \
     check_contradictions, library_load, check_tautologies, negate_target

def main(stdscr):
    screen = Screen() # object representing console/windows
    tl = TreeList() # object representing lists of parsed statements
    ad = AutoDict() # get initial automation dictionary containing basic axioms
    started = False # whether automated cleanup is started
    ttree = None # track which targets have been proved
    num_checked = 0 # number of hypotheses that have been checked for contradictions
    deps = [] # variables that subsequent skolemizations will depend on
    skip = False # whether to skip checking completion
    reset = False # whether to reset dependencies

    while True:
        if not started:
            num_checked = 0
        c = stdscr.getkey()
        if c == '\t': # TAB = switch window focus (and associated pad)
            skip = True
            screen.switch_window()
            tl.switch_list()
        elif c == '\x1b' or c == 'q': # ESC or q = quit
            response = edit(screen, "Exit (y/n): ", 12)
            if response and response[12:] == "y" or response[12:] == "Y":
                break
            skip = True
        elif c == 'e': # e = edit
            line = tl.focus.line
            data = '' if line == tl.focus.len() else repr(tl.focus.data[line])
            tree = get_text(screen, data) # parse text from user
            if tree:
                tl.focus[line] = tree # insert tree in treelist
                screen.focus[line] = str(tree) # insert unicode string into pad
            screen.focus.refresh()
        # elif c == 'a': # a = automate
        #    automate(screen, tl, ad)
        elif c == 'v': # equivalence
            equality(screen, tl)
        elif c == 's': # start automated cleanup
            started = True
            skip = False
            ttree = TargetNode(-1, [TargetNode(i) for i in range(0, len(tl.tlist2.data))])
        elif c == 'p': # modus ponens
            modus_ponens(screen, tl, ttree, deps)
        elif c == 't': # modus tollens
            modus_tollens(screen, tl, ttree, deps)
        elif c == 'n': # negate target
            negate_target(screen, tl)
        elif c == 'w': # write to library
            skip = True
            if not started:
                library_export(screen, tl)
        elif c == 'r': # read from library
            library_import(screen, tl)
        elif c == 'l': # load from library as tableau
            reset = True
            # check tableau is currently empty
            if not tl.tlist0.data and not tl.tlist1.data and not tl.tlist2.data:
                library_load(screen, tl)
            else:
                screen.dialog("Tableau must be empty before loading problem")
        elif c == 'c': # clear_tableau
            clear_tableau(screen, tl)
            started = False
            ttree = None
            num_checked = 0
            deps = []
            reset = True
        elif c == 'KEY_RIGHT':
            skip = True
            pad = screen.focus
            pad.cursor_right()
            pad.refresh()
        elif c == 'KEY_LEFT':
            skip = True
            pad = screen.focus
            pad.cursor_left()
            pad.refresh()
        elif c == 'KEY_DOWN':
            skip = True
            pad = screen.focus
            if pad != screen.pad0 and tl.focus.line != tl.focus.len():
                pad.cursor_down()
                pad.refresh()
                tl.focus.line += 1
        elif c == 'KEY_UP':
            skip = True
            pad = screen.focus
            if pad != screen.pad0 and tl.focus.line != 0:
                pad.cursor_up()
                pad.refresh()
                tl.focus.line -= 1
        if started: # automated cleanup
            if not skip:
                deps = cleanup(screen, tl, ttree)
                num_checked = check_contradictions(screen, tl, num_checked, ttree)
                check_tautologies(screen, tl, ttree)
                if targets_proved(screen, tl, ttree):
                    screen.dialog("All targets proved")
                    started = False
            skip = False
            if reset:
                # reset dependencies
                tl.tlist1.dep = dict()
                reset = False
    screen.exit()

wrapper(main) # curses wrapper handles exceptions
