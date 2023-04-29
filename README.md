# Python GOFAI scripts

These scripts are to rapidly iterate on GOFAI ideas in Python.

Prerequisites: Python 3.8, parsimonious, curses

To install parsimonious:

pip install parsimonious

To run the interface:

python main.py

Interface commands:

* &lt;TAB&gt; = switch windows
* &lt;LEFT&gt;/&lt;RIGHT&gt;&lt;UP&gt;&lt;DOWN&gt; = move cursor
* e = edit mode
* m = manual mode
* q = quit

Editor commands:

* &lt;INS&gt; = insert/replace
* &lt;DEL&gt; = delete char under cursor
* &lt;BACKSPACE&gt; = delete character before cursor
* &lt;LEFT&gt;/&lt;RIGHT&gt; = move cursor
* &lt;ENTER&gt; = finish editing

Manual mode commands:

* p = modus ponens
* t = modus tollens
* w = write to the library
* r = read from the library
* n = new theorem, clears the tableau
* a = automation
* s = skolemize, create metavariables and move quantors to quantifier zone
* &lt;ESC&gt; = quit

The various moves are used as follows:

* Automation: keep pressing a key until the state stops changing. Almost no
  automation whatsoever is provided at this point. More to come soon!
* Modus Ponens: either navigate to an implication whose antecedent is in the
  list of hypotheses and press Enter, then navigate to the antecedent and press
  Enter, or navigate to an implication whose consequent is in the targets and
  press Enter, then navigate to the consequent and press Enter.
* Modus Tollens: either navigate to an implication the negation of whose
  consequent is in the hypotheses and press Enter, then navigate to the
  negation of the consequent and press Enter, or navigate to an implication
  the negation of whose antecedent is in the targets and press Enter, then
  navigate to the negation of the antecedent.
* Library write. The proposition must not have been skolemized. You will be
  prompted to enter a title for the proposition and then you will be prompted
  to enter tags which must begin with a # symbol, e.g. #algebra, #inequalities, 
  #iff, #\mathbb{N}
* Library read. You will be prompted to enter at least one tag to narrow the
  search. If you know the first letter of the title you can press that to
  further restrict the search. Search by pressing the up and down cursor keys
  and then press Enter to select.

&lt;ESC&gt; cancels application of a move.
