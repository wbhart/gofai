
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
def move_clicked(n):
	print("Move", n, "clicked")

@eel.expose	
def quantifier_clicked(n):
	print("Quantifier", n, "clicked")

@eel.expose	
def hypothesis_clicked(n):
	print("Hypothesis", n, "clicked")

@eel.expose	
def target_clicked(n):
	print("Target", n, "clicked")

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
	print("New proof started")
	text = eel.dialog("Enter a target in LaTeX format:")()
	if not text:
		return

	global quantifiers
	quantifiers = []
	eel.populate_quantifiers(quantifiers)

	global hypothesis
	hypothesis = []
	eel.populate_hypothesis(hypothesis)

	global targets
	targets = [text]
	eel.populate_targets(targets)

	eel.status("Proof in progress, select move or library result.")

@eel.expose	
def restart_proof():
	print("Proof restarted")

@eel.expose	
def export_proof():
	print("Proof exported")





# callback when interface window is closed
def interface_closed(path, open):
	print("Closed page", path)
	print(len(open), "more websockets running")
	exit()

# start the webserver at localhost:8000 and launch the detected default browser
eel.start("interface.html", mode = "default", close_callback = interface_closed)

