
import eel

# initialize eel
eel.init("web")

# keep track of state
library = []
quantifiers = []
hypothesis = []
targets = []

# expose python functions to the javascript code

@eel.expose	
def add_quantifier():
	text = eel.dialog("Enter a quantifier in LaTeX format:")()
	if not text:
		return

	global quantifiers
	quantifiers.append(text)
	eel.populate_quantifiers(quantifiers)
	print("Quantifier added")

@eel.expose	
def add_hypothesis():
	text = eel.dialog("Enter a hypothesis in LaTeX format:")()
	if not text:
		return

	global hypothesis
	hypothesis.append(text)
	eel.populate_hypothesis(hypothesis)
	print("Hypothesis added")

@eel.expose	
def add_target():
	text = eel.dialog("Enter a target in LaTeX format:")()
	if not text:
		return

	global targets
	targets.append(text)
	eel.populate_targets(targets)
	print("Target added")

@eel.expose	
def move_clicked(n):
	print("Move", n, "clicked")

@eel.expose	
def quantifier_clicked(n):
	global quantifiers
	assert n < len(quantifiers)
	text = eel.dialog("Edit the quantifier in LaTeX format:", quantifiers[n])()
	if text == "":
		del quantifiers[n]
		print("Quantifier", n ,"deleted")
	elif not text:
		return
	else:
		quantifiers[n] = text
		print("Quantifier", n ,"edited")

	eel.populate_quantifiers(quantifiers)

@eel.expose	
def hypothesis_clicked(n):
	global hypothesis
	assert n < len(hypothesis)
	text = eel.dialog("Edit the hypothesis in LaTeX format:", hypothesis[n])()
	if text == "":
		del hypothesis[n]
		print("Hypothesis", n ,"deleted")
	elif not text:
		return
	else:
		hypothesis[n] = text
		print("Hypothesis", n ,"edited")

	eel.populate_hypothesis(hypothesis)

@eel.expose	
def target_clicked(n):
	global targets
	assert n < len(targets)
	text = eel.dialog("Edit the target in LaTeX format:", targets[n])()
	if text == "":
		del targets[n]
		print("Target", n ,"deleted")
	elif not text:
		return
	else:
		targets[n] = text
		print("Target", n ,"edited")

	eel.populate_targets(targets)
	
@eel.expose	
def library_clicked(n):
	print("Library suggestion", n, "clicked")
	assert(n < len(library))
	global hypothesis
	hypothesis.append(library[n])
	eel.populate_hypothesis(hypothesis)

@eel.expose	
def library_search(query):
	print("Library searched for:", query)
	results = []
	if query:
		results.append(query + " in this context")
		results.append(query + " also in that context")
	global library
	library = results
	eel.populate_library(library)

@eel.expose	
def new_proof():
	global quantifiers
	quantifiers = []
	eel.populate_quantifiers(quantifiers)

	global hypothesis
	hypothesis = []
	eel.populate_hypothesis(hypothesis)

	global targets
	targets = []
	eel.populate_targets(targets)

	eel.edit_mode(True)

@eel.expose	
def start_proof():
	eel.edit_mode(False)
	print("Proof started")

@eel.expose	
def export_proof():
	print("Proof exported")




# python stuff

# callback when interface window is closed
def interface_closed(path, open):
	print("Closed page", path)
	print(len(open), "more websockets running")
	exit()

# start the webserver at localhost:8000 and launch the detected default browser
eel.start("interface.html", mode = "default", close_callback = interface_closed)

