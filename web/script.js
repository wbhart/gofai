
// --- Functions exposed to python ---

// display the given string and wait for acknowledgement from the user
eel.expose(info);
function info(str) {
	alert(str);
}

// display the given string and wait for user string input
eel.expose(dialog);
function dialog(str, def = "") {
	return prompt(str, def);
}

// display the given string in the status area
eel.expose(status);
function status(str) {
	document.getElementById("status").innerHTML = str;
}

// populate list of displayed library results
eel.expose(populate_library)
function populate_library(list) {
	var div = document.getElementById("lib-box").getElementsByClassName("box-body")[0];
	div.innerHTML = "";

	for (let i = 0; i < list.length; i++) {
		var line = document.createElement('div');
		// line.classList.add("line", "entry")
        line.classList.add("line", "entry", "autocomplete-item");
	 
		line.onclick = function() {library_clicked(i)};
		line.innerHTML = list[i];

		div.appendChild(line);
	}
	
}

// populate quantifier zone
eel.expose(populate_quantifiers)
function populate_quantifiers(list) {
	var div = document.getElementById("quant-box").getElementsByClassName("box-body")[0];
	div.innerHTML = "";

	for (let i = 0; i < list.length; i++) {
		var line = document.createElement('div');
		line.classList.add("line", "quant");
		line.onclick = function() {quantifier_clicked(i)};

		var name = document.createElement('span');
		name.classList.add("zone-line-name");
		name.innerHTML = "\\(\\bf Q_" + (i+1) + "\\)";

		line.appendChild(name);
		line.innerHTML += list[i];
		div.appendChild(line);
	}
	MathJax.typeset();
}

// populate hypothesis zone
eel.expose(populate_hypothesis)
function populate_hypothesis(list) {
	var div = document.getElementById("hyp-box").getElementsByClassName("box-body")[0];
	div.innerHTML = "";

	for (let i = 0; i < list.length; i++) {
		var line = document.createElement('div');
		line.classList.add("line", "hyp");
		line.onclick = function() {hypothesis_clicked(i)};

		var name = document.createElement('span');
		name.classList.add("zone-line-name");
		name.innerHTML = "\\(\\bf H_" + (i+1) + "\\)";

		line.appendChild(name);
		line.innerHTML += list[i];
		div.appendChild(line);
	}
	MathJax.typeset();
}

// populate target zone
eel.expose(populate_targets)
function populate_targets(list) {
	var div = document.getElementById("targ-box").getElementsByClassName("box-body")[0];
	div.innerHTML = "";

	for (let i = 0; i < list.length; i++) {
		var line = document.createElement('div');
		line.classList.add("line", "target");
		line.onclick = function() {target_clicked(i)};

		var name = document.createElement('span');
		name.classList.add("zone-line-name");
		name.innerHTML = "\\(\\bf T_" + (i+1) + "\\)";

		line.appendChild(name);
		line.innerHTML += list[i];
		
		div.appendChild(line);
	}
	MathJax.typeset();
}

// enables and disables edit mode, initially enabled.
eel.expose(edit_mode)
function edit_mode(edit) {
	add_buttons = document.getElementsByClassName("add");
	moves_box = document.getElementById("moves-box");
	if (edit) {
		status("Edit mode, press start proof when tableau is ready")
		for (button of add_buttons) { button.style.display = "block"; }
		moves_box.classList.add("disabled")
	} else {
		status("Proof mode, select move or library result to progress")
		for (button of add_buttons) { button.style.display = "none"; }
		moves_box.classList.remove("disabled")
	}
}

// --- Functions forwarding to python ---

function add_quantifier() {
	eel.add_quantifier();
}

function add_hypothesis() {
	eel.add_hypothesis();
}

function add_target() {
	eel.add_target();
}

function quantifier_clicked(n) {
	console.log("quantifier " + n +  " clicked!");
	eel.quantifier_clicked(n);
}

function hypothesis_clicked(n) {
	console.log("hypothesis " + n +  " clicked!");
	eel.hypothesis_clicked(n);
}

function target_clicked(n) {
	console.log("target " + n +  " clicked!");
	eel.target_clicked(n);
}

function move_clicked(n) {
	console.log("move " + n +  " clicked!");
	eel.move_clicked(n);
}

function library_clicked(n) {
	console.log("library line " + n +  " clicked!");
	eel.library_clicked(n);
}

function library_search(str) {
	console.log("search library for: " + str)
	eel.library_search(str);
}

function new_proof() {
	console.log("new proof!");
	eel.new_proof();
}

function start_proof() {
	console.log("start proof!");
	eel.start_proof();
}

function export_proof() {
	console.log("export proof!");
	eel.export_proof();
}


