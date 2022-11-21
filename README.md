# Python GOFAI scripts

These scripts are to rapidly iterate on GOFAI ideas in Python.

Prerequisites: Python 3.8, parsimonious, curses

To install parsimonious:

pip install parsimonious

To run the editor:

python main.py

Interface commands:

* <TAB> = switch windows
* e = edit mode

Editor commands:

* &lt;INS&gt; = insert/replace
* &lt;DEL&gt; = delete char under cursor
* &lt;BACKSPACE&gt; = delete character before cursor
* &lt;LEFT&gt;/&lt;RIGHT&gt; = move cursor
* &lt;ENTER&gt; = finish editing

There is currently also a parser, but it is not hooked up to the editor. To run it, go into
the parser directory, run Python and type:

import input_parser

input_parser.parse_input()

A prompt will be displayed at which you can type an input to be parsed, e.g.

\forall x \exists k \neg((3 + 7k^4) - 7j = (8k + f(7s + 1)) + 3k - 1 \wedge 4k > f(23 + k, 3k^3) \implies x = 3k)


