
## JavaScript Functions Exposed to Python:

`status(str) -> none`  
set the displayed status message to the string

`info(str) -> none`  
display the given string and wait for user acknowledgement

`dialog(str) -> str/none`  
display the given string and wait for user string input, returns input unless cancelled

`populate_library([str]) -> none`  
set the list of displayed lines in the library results

`populate_quantifiers([str]) -> none`  
set the list of displayed lines in the quantifier zone

`populate_hypothesis([str]) -> none`  
set the list of displayed lines in the hypothesis zone

`populate_targets([str]) -> none`  
set the list of displayed lines in the target zone

## Expected Python Functions Exposed to JavaScript

`move_clicked(int) -> none`  
called when a move is clicked, passing the move type  
(0 = Modus Ponens, 1 = Modus Tollens, 2 = Skolomize, 3 = Automation)

`qunatifier_clicked(int) -> none`  
called when a line in the qunatifier zone is clicked, passing the line number (0-indexed)

`hypothesis_clicked(int) -> none`  
called when a line in the hypothesis zone is clicked, passing the line number (0-indexed)

`target_clicked(int) -> none`  
called when a line in the target zone is clicked, passing the line number (0-indexed)

`library_clicked(int) -> none`  
called when a library suggestion is clicked, passing the line number (0-indexed)

`library_search(str) -> none`  
called whenever the string in the library search field changes, passing the current string

`new_proof() -> none`  
called when the "new proof" button is clicked

`restart_proof() -> none`  
called when the "restart proof" button is clicked

`export_proof() -> none`  
called when the "export proof" button is clicked

## ToDo-List

### Protocol Improvements
- pass library serach results as python dicts, with fields for title, preview, tags, etc
- pass mathematical terms as trees (python dicts) to allow selection of subexpressions
- pass information as to what is currently clickable/selectable
- use unique identifiers instead of line numbers (to allow reordering/sorting)

### Design Improvements
- highlighting when selecting lines during a move
- greying out things not currently clickable/selectable
- allow reordering/sorting of lines
- add tutorial/instructions
