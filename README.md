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

* <INS> = insert/replace
* <DEL> = delete char under cursor
* <BACKSPACE> = delete character before cursor
* <LEFT>/<RIGHT> = move cursor
* <ENTER> = finish editing

There is currently also a parser, but it is not hooked up to the editor. To run it, go into
the parser directory, run Python and type:

import input_parser

input_parser.parse_input()

A prompt will be displayed at which you can type an input to be parsed, e.g.

(3 + 7k^4) - 7j = (8k + f(7s + 1)) + 3k - 1 \wedge 4k > f(23 + k, 3k^3)


