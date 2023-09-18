
eel.expose(javascript_alert); // expose javascript function to python
function javascript_alert(str) {
	alert(str);
}

function clicked() {
	str = document.getElementById('text').value;
	eel.python_reverse_string(str); // call exposed python function
}