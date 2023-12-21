from flask import Flask, render_template
from flask_socketio import SocketIO, emit
from tree import TreeList
from logic import modus_ponens, modus_tollens, cleanup, clear_tableau, filter_library, \
     library_load, fill_macros, library_import, equality_substitution
from utility import filter_titles, initialise_sorts, type_vars, process_sorts, \
     TargetNode, target_compatible, update_constraints, process_sorts, complement_tree, \
     trim_spaces, find_all
from moves import check_targets_proved
from nodes import ForallNode, IffNode, ImpliesNode, AndNode, EqNode
from parser import statement, StatementVisitor
from parsimonious import exceptions
import json

screen = None # dummy screen parameter
tl = None # tableau
ttree = None # target dependency tree
filtered_titles = None # (filepos, title) pairs filtered from library
impl = None # implication in modus_ponens/tollens
equ = None # equality in rewrite
pred_list = None # list of predicates to use in modus ponens/tollens
predicate = None # predicate being used in mp/mt
num_preds = 0 # number of predicates selected
preds_needed = 0 # number of predicates needed in modus ponens/tollens
forward = True # whether we are forwards or backwards reasoning
move = 0 # move 0 = init, 1 = started, 2 = mp, 3 = mt, 4 = rewrite, 5 = library import
pane_dict = dict()

def to_ast(screen, string):
    try:
        ast = statement.parse(string) # parse input
        visitor = StatementVisitor()
        return visitor.visit(ast), ""
    except exceptions.IncompleteParseError as inst:
        index = inst.args[1]
        return index, f"Extra characters on line, starting at column {str(index + 1)}."
    except exceptions.ParseError as inst:
        index = inst.pos
        return index, f"Error in statement starting at column {str(index + 1)}."

def initialize():
    global tl
    global ttree
    global pane_dict

    tl = TreeList() # object representing tableau
    ttree = None # track which targets have been proved

    pane_dict['quantifierZone'] = tl.tlist0
    pane_dict['hypothesisZone'] = tl.tlist1
    pane_dict['targetZone'] = tl.tlist2

def autocleanup(screen, tl, ttree):
    dirty1, dirty2 = cleanup(screen, tl, ttree)
    fill_macros(screen, tl)
    ok, error = update_constraints(screen, tl)
    if ok:
        ok, error = process_sorts(screen, tl)
        if not ok:
            emit('error', {'msg' : error, 'restart' : True})
            return
    else:
        emit('error', {'msg' : error, 'restart' : True})
        return
    dirtytxt0 = str(tl.tlist0.data[0]) if tl.tlist0.data else ''
    dirtytxt1 = [str(tl.tlist1.data[i]) for i in dirty1]
    dirtytxt2 = [str(tl.tlist2.data[i]) for i in dirty2]
    emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
         'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2})
    dirty1, dirty2, done, plist = check_targets_proved(screen, tl, ttree)
    dirtytxt0 = str(tl.tlist0.data[0]) if tl.tlist0.data else ''
    dirtytxt1 = [str(tl.tlist1.data[i]) for i in dirty1]
    dirtytxt2 = [str(tl.tlist2.data[i]) for i in dirty2]
    emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
         'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2})
    for i in plist:
        msg = 'Target '+str(i)+' proved!'
        emit('error', {'msg' : msg, 'restart' : False})
    if done:
        emit('done')
        move = 0
    
app = Flask(__name__)
socketio = SocketIO(app, cors_allowed_origins="*")

@app.route('/')
def index():
    return render_template('index.html')  # You'll create this HTML file

@socketio.on('send_line')
def handle_send_line(data):
    global screen
    global tl
    global pane_dict
    print("Received data:", data)  # Add this line for debugging
    pane_id = data['paneId']
    pane = pane_dict[pane_id]
    line_number = data['lineNumber']
    text = data['text']
            
    if line_number < len(pane.data) or (text != '' and line_number == len(pane.data)):
        # Call parse_line function and update tableau (tl) accordingly
        tree, msg = to_ast(screen, text)
        if isinstance(tree, int):
            # error out
            emit('edit_error', {'paneId': pane_id, 'lineNumber': line_number, 'msg': msg})
        else:
            pane[line_number] = tree
            updated_line = str(pane.data[line_number])  # Adjust according to pane_id
            emit('update_line', {'paneId': pane_id, 'lineNumber': line_number, 'updatedText': updated_line})
    
@socketio.on('clear_tableau')
def handle_clear_tableau():
    global screen
    global tl
    global ttree
    clear_tableau(screen, tl)
    ttree = None
    
@socketio.on('fetch_line_content')
def handle_fetch_line_content(data):
    global pane_dict
    pane_id = data['paneId']
    line_number = data['lineNumber']
    pane = pane_dict[pane_id]
    content = repr(pane.data[line_number]) if line_number < len(pane.data) else ''

    # Send content back to client
    emit('fill_line_content', {'paneId': pane_id, 'lineNumber': line_number, 'content': content})

@socketio.on('request_library_filter')
def handle_request_library_filter(data):
    global screen
    global tl
    global filtered_titles
    tags = "Tags: "+data['tags']
    letter = data['letter']
    print("filter tags:"+tags+", letter:"+letter)
    library = open("library.dat", "r")
    filtered_titles = filter_library(screen, tl, library, tags)
    library.close()
    if letter != '':
        filtered_titles = filter_titles(filtered_titles, letter)
    strings = [v[1] for v in filtered_titles]
    emit('update_dropdown', {'strings': strings})

@socketio.on('mp_start')
def handle_modus_ponens(data):
    global screen
    global tl
    global impl
    global move
    global num_preds
    global pred_list
    line1 = data['lineNumber']
    impl = line1
    t = tl.tlist1.data[line1]
    while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
        t = t.left
    if not isinstance(t, ImpliesNode) and not isinstance(t, IffNode): # no implication after quantifiers
        emit('error', {'msg' : 'Not an implication', 'restart' : False})
    else:
        move = 2
        num_preds = 0
        pred_list = []
        emit('get_predicate', 1)

@socketio.on('mt_start')
def handle_modus_tollens(data):
    global screen
    global tl
    global impl
    global move
    global num_preds
    global pred_list
    line1 = data['lineNumber']
    impl = line1
    t = tl.tlist1.data[line1]
    while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
        t = t.left
    if not isinstance(t, ImpliesNode) and not isinstance(t, IffNode): # no implication after quantifiers
        emit('error', {'msg' : 'Not an implication', 'restart' : False})
    else:
        move = 3
        num_preds = 0
        pred_list = []
        emit('get_predicate', 1)

@socketio.on('select_predicate')
def handle_select_predicate(data):
    global screen
    global tl
    global ttree
    global impl
    global num_preds
    global pred_list
    global preds_needed
    global forward
    paneId = data['paneId']
    line2 = data['lineNumber']
    isforward = paneId == 'hypothesisZone'
    pred_list.append(line2)
    num_preds += 1
    if num_preds == 1:
        forward = isforward
        preds_needed = 1
        t = tl.tlist1.data[impl]
        while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
            t = t.left
        if move == 2:
            t = t.left if forward else t.right
        if move == 3:
            t = t.right if forward else t.left
            t = complement_tree(t) # modus tollens unifies with complement
        while isinstance(t, ForallNode): # implication is assumed to have only forall quantifiers
            t = t.left
        while isinstance(t, AndNode):
            t = t.left
            preds_needed += 1
    elif forward != isforward:
        msg = 'Predicates must all be hypotheses or all targets'
        emit('error', {'msg' : msg, 'restart' : False})
        return    
    if num_preds < preds_needed:
        emit('get_predicate', num_preds + 1)
    else:
        # check everything is target compatible
        dep = tl.tlist1.dependency(impl)
        for i in range(len(pred_list)):
            line2 = pred_list[i]
            dep = target_compatible(screen, tl, ttree, dep, line2, forward)
            if not dep:
                if len(pred_list) == 1:
                    emit('error', {'msg' : 'Not target compatible', 'restart' : False})
                else:
                    msg = 'Predicate '+str(i)+' not target compatible'
                    emit('error', {'msg' : msg, 'restart' : False})
                return
        # run modus ponens/tollens
        if move == 2:
            success, dirty1, dirty2 = modus_ponens(screen, tl, ttree, dep, impl, pred_list, forward)
        elif move == 3:
            success, dirty1, dirty2 = modus_tollens(screen, tl, ttree, dep, impl, pred_list, forward)
        if not success:
            emit('error', {'msg' : 'Predicate does not match implication', 'restart' : False})
        else:
            dirtytxt0 = str(tl.tlist0.data[0]) if tl.tlist0.data else ''
            dirtytxt1 = [str(tl.tlist1.data[i]) for i in dirty1]
            dirtytxt2 = [str(tl.tlist2.data[i]) for i in dirty2]
            emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
                 'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2})
            autocleanup(screen, tl, ttree)

@socketio.on('rewrite_start')
def handle_rewrite(data):
    global screen
    global tl
    global equ
    line1 = data['lineNumber']
    equ = line1
    t = tl.tlist1.data[line1]
    while isinstance(t, ForallNode):
        t = t.left
    if not isinstance(t, EqNode): # not an equality
        emit('error', {'msg' : 'Not an equality', 'restart' : False})
    else:
        move = 4
        emit('get_selection')

@socketio.on('rewrite_selection')
def handle_rewrite_selection(data):
    global screen
    global tl
    global ttree
    global equ
    hyp = data['paneId'] == 'hypothesisZone'
    line2 = data['lineNumber']
    start = data['start']
    end = data['end']
    if hyp:
        tlist = tl.tlist1.data
    else:
        tlist = tl.tlist2.data
    string = str(tlist[line2])
    start, sub_string = trim_spaces(string, start, end)
    if sub_string == '':
        emit('error', {'msg' : 'Empty selection', 'restart' : False})
    else:
        idx = find_all(string, sub_string)
        n = idx.index(start) # which occurence of substring do we want (0-indexed)
        if not equality_substitution(screen, tl, equ, line2, hyp, sub_string, n):
            emit('error', {'msg' : 'Equality cannot be applied', 'restart' : False})
        else:
            if hyp:
                dirty1 = [line2]
                dirty2 = []
            else:
                dirty1 = []
                dirty2 = [line2]
            dirtytxt0 = str(tl.tlist0.data[0]) if tl.tlist0.data else ''
            dirtytxt1 = [str(tl.tlist1.data[i]) for i in dirty1]
            dirtytxt2 = [str(tl.tlist2.data[i]) for i in dirty2]
            emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
                 'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2})
            autocleanup(screen, tl, ttree)

@socketio.on('library_load')
def handle_library_load(data):
    global screen
    global tl
    global filtered_titles
    selected_string = data['selectedString']
    library = open("library.dat", "r")
    for filepos, title in filtered_titles:
        if title == selected_string:
            dirty1, dirty2 = library_load(screen, tl, library, filepos)
            dirtytxt0 = str(tl.tlist0.data[0]) if tl.tlist0.data else ''
            dirtytxt1 = [str(tl.tlist1.data[i]) for i in dirty1]
            dirtytxt2 = [str(tl.tlist2.data[i]) for i in dirty2]
            library.close()
            emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
                 'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2})
            return
    library.close()

@socketio.on('library_import')
def handle_library_import(data):
    global screen
    global tl
    global filtered_titles
    global move
    selected_string = data['selectedString']
    library = open("library.dat", "r")
    move = 5
    for filepos, title in filtered_titles:
        if title == selected_string:
            ok = library_import(screen, tl, library, filepos)
            library.close()
            if ok:
                dirty1 = [len(tl.tlist1.data) - 1]
                dirty2 = []
                dirtytxt0 = str(tl.tlist0.data[0]) if tl.tlist0.data else ''
                dirtytxt1 = [str(tl.tlist1.data[i]) for i in dirty1]
                dirtytxt2 = []
                emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
                     'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2})
                autocleanup(screen, tl, ttree)
                return
    library.close()

@socketio.on('start')
def handle_start():
    global screen
    global tl
    global ttree
    global move
    fill_macros(screen, tl)
    type_vars(screen, tl)
    initialise_sorts(screen, tl)
    ok, error = process_sorts(screen, tl)
    if ok:
        ttree = TargetNode(-1, [TargetNode(i) for i in range(0, len(tl.tlist2.data))])
        dirty1 = [i for i in range(len(tl.tlist1.data))]
        dirty2 = [i for i in range(len(tl.tlist2.data))]
        dirtytxt0 = str(tl.tlist0.data[0]) if tl.tlist0.data else ''
        dirtytxt1 = [str(tl.tlist1.data[i]) for i in dirty1]
        dirtytxt2 = [str(tl.tlist2.data[i]) for i in dirty2]
        move = 1
        emit('update_dirty', {'dirtytxt0': dirtytxt0, 'dirty1': dirty1, \
             'dirtytxt1': dirtytxt1, 'dirty2': dirty2, 'dirtytxt2': dirtytxt2})
    else:
        emit('error', {'msg' : error, 'restart' : True})

if __name__ == '__main__':
    initialize()
    socketio.run(app, host='0.0.0.0', port=9001, debug=True)
