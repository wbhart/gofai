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
* q = quit

The various moves are used as follows:

* Modus Ponens: navigate to an implication whose precedent is in the list of
  hypotheses and press Enter.

