import curses # console library
import curses.ascii # ascii classification
from interface import Screen, iswide_char, nchars_to_chars
from curses import wrapper
from editor import get_text, edit
from tree import TreeList
from moves import cleanup, modus_ponens, modus_tollens, library_export, \
     library_import, clear_tableau, equality_substitution, targets_proved, \
     library_load, fill_macros, convert, show_prune
from utility import TargetNode, initialise_sorts, type_vars, process_sorts, \
     update_constraints, prune_move_list
from automation import automate

def main(stdscr):
    screen = Screen() # object representing console/windows
    tl = TreeList() # object representing tableau
    started = False # whether automated cleanup is started
    ttree = None # track which targets have been proved
    skip = False # whether to skip checking completion
    reset = False # whether to reset dependencies
    done = False # whether the theorem has been proved

    while True:
        c = stdscr.getkey()
        if c == '\t': # TAB = switch window focus (and associated pad)
            skip = True
            screen.switch_window()
            tl.switch_list()
        elif c == '\x1b' or c == 'q': # ESC or q = quit
            response = edit(screen, "Exit (y/n): ", 12, True)
            if response and (response[12:] == "y" or response[12:] == "Y"):
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
        elif c == 'v': # equivalence
            if started:
                equality_substitution(screen, tl)
        elif c == 's': # start automated cleanup
            if not started:
                fill_macros(screen, tl)
                type_vars(screen, tl)
                initialise_sorts(screen, tl)
                ok, error = process_sorts(screen, tl)
                if ok:
                    started = True
                    skip = False
                    ttree = TargetNode(-1, [TargetNode(i) for i in range(0, len(tl.tlist2.data))])
                else:
                    screen.dialog(error)
        elif c == 'a': # automation
            if started:
                if automate(screen, tl, ttree):
                    screen.dialog("All targets proved!")
                    screen.dialog(str(len(tl.tlist1.data))+" lines")
                    done = True
                else:
                    screen.dialog("Unable to prove theorem.")
                skip = True
        elif c == 'p': # modus ponens
            if started:
                modus_ponens(screen, tl, ttree)
        elif c == 't': # modus tollens
            if started:
                modus_tollens(screen, tl, ttree)
        # elif c == 'n': # negate target
        #    negate_target(screen, tl)
        elif c == 'w': # write to library
            skip = True
            if not started:
                library_export(screen, tl)
        elif c == 'r': # read from library
            if started:
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
            done = False
            ttree = None
        elif c == 'd': # debug
            skip = True
            screen.debug_on = not screen.debug_on
        elif c == 'z': # rewrite library
            convert(screen, tl)
        elif c == 'n': # prune proof
            if done:
                (hyps, tars) = prune_move_list(screen, tl, ttree)
                new_tl = TreeList()
                show_prune(screen, tl, new_tl, hyps, tars)
                ttree = None
                tl = new_tl
                done = False
                skip = True
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
        else:
            skip = True
        if started: # automated cleanup
            if not skip:
                cleanup(screen, tl, ttree)
                fill_macros(screen, tl)
                ok, error = update_constraints(screen, tl)
                if ok:
                    ok, error = process_sorts(screen, tl)
                    if ok:
                        done, plist = targets_proved(screen, tl, ttree)
                        for i in plist:
                            screen.dialog("Target "+str(i)+" proved!")
                        screen.focus.refresh()
                        if done:
                            screen.dialog("All targets proved")
                            done = True
                            started = False
                    else:
                        screen.dialog(error)
                        started = False
                else:
                    screen.dialog(error)
                    started = False
            skip = False
            if reset:
                # reset dependencies
                tl.tlist1.dep = dict()
                reset = False
    screen.exit()

wrapper(main) # curses wrapper handles exceptions
