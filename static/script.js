var socket = io.connect('http://127.0.0.1:9001');

var isUpdatingContent = false; // Whether an editable div is having its content updated
var isEditError = false; // Whether an editable div is having its content updated
var mode = 0; // What mode are we in? -1 = done, 0 = init, 1 = started, 2 = mp, 3 = mt, 4 = rewrite, 5 = import, 6 = automation
var mmode = 0; // modus ponens/tollens step, 0 = get implication, 1 = get predicate
var rmode = 0; // rewrite step, 0 = get equality, 1 = get selection
var error_line = -1; // line edit error is unresolved

function updateStatus(message) {
    var statusElement = document.getElementById('status');
    statusElement.innerText = message;
} 

function switch_mode(new_mode) {
   // mode -1 = done, 0 = init, 1 = started, 2 = mp, 3 = mt, 4 = rewrite, 5 = import, 6 = automation
   mode = new_mode;
   switch (mode) {
       case -1:
           document.getElementById('loadButton').disabled = true;
           document.getElementById('clearButton').disabled = false;
           document.getElementById('startButton').disabled = true;
           document.getElementById('automateButton').disabled = true;
           document.getElementById('modusPonensButton').disabled = true;
           document.getElementById('modusTollensButton').disabled = true;
           document.getElementById('rewriteButton').disabled = true;
           document.getElementById('importButton').disabled = true;
           document.getElementById('cancelButton').disabled = true;
           break;
       case 0:
           allowEdit();
           document.getElementById('loadButton').disabled = false;
           document.getElementById('clearButton').disabled = false;
           document.getElementById('startButton').disabled = false;
           document.getElementById('automateButton').disabled = true;
           document.getElementById('modusPonensButton').disabled = true;
           document.getElementById('modusTollensButton').disabled = true;
           document.getElementById('rewriteButton').disabled = true;
           document.getElementById('importButton').disabled = true;
           document.getElementById('cancelButton').disabled = true;
           break;
       case 1:
           noEdit();
           document.getElementById('loadButton').disabled = true;
           document.getElementById('clearButton').disabled = false;
           document.getElementById('startButton').disabled = true;
           document.getElementById('automateButton').disabled = false;
           document.getElementById('modusPonensButton').disabled = false;
           document.getElementById('modusTollensButton').disabled = false;
           document.getElementById('rewriteButton').disabled = false;
           document.getElementById('importButton').disabled = false;
           document.getElementById('cancelButton').disabled = true;
           break;
       case 2:
       case 3:
       case 4:
       case 5:
           document.getElementById('loadButton').disabled = true;
           document.getElementById('clearButton').disabled = true;
           document.getElementById('startButton').disabled = true;
           document.getElementById('automateButton').disabled = true;
           document.getElementById('modusPonensButton').disabled = true;
           document.getElementById('modusTollensButton').disabled = true;
           document.getElementById('rewriteButton').disabled = true;
           document.getElementById('importButton').disabled = true;
           document.getElementById('cancelButton').disabled = false;
           break;
        case 6:
           document.getElementById('loadButton').disabled = true;
           document.getElementById('clearButton').disabled = true;
           document.getElementById('startButton').disabled = true;
           document.getElementById('automateButton').disabled = true;
           document.getElementById('modusPonensButton').disabled = true;
           document.getElementById('modusTollensButton').disabled = true;
           document.getElementById('rewriteButton').disabled = true;
           document.getElementById('importButton').disabled = true;
           document.getElementById('cancelButton').disabled = true;
       
   }
}

function handleFocus(event) {
    var parentPane = this.parentElement;
    var divsArray = Array.from(parentPane.querySelectorAll('div'));
    var index = divsArray.indexOf(this); // Find the index of the current div
    var paneId = parentPane.id;
    switch (mode) {
        case 0:
            if (!isUpdatingContent && !isEditError) {
                fetchAndFillContent(this, index); // Function to fetch content from Python
            }
            break;
        case 2:
            event.target.blur();
            if (paneId === 'hypothesisZone') {
                switch (mmode) {
                    case 0:
                        this.style.color = 'blue';
                        socket.emit('mp_start', { lineNumber: index });
                        break;
                    case 1:
                        this.style.color = 'blue';
                        socket.emit('select_predicate', { paneId: paneId, lineNumber: index });
                        break;
                }
            }
            if (paneId === 'targetZone') {
                switch (mmode) {
                    case 1:
                        this.style.color = 'blue';
                        socket.emit('select_predicate', { paneId: paneId, lineNumber: index });
                        break; 
                }
            }
            break;
        case 3:
            event.target.blur();
            if (paneId === 'hypothesisZone') {
                switch (mmode) {
                    case 0:
                        this.style.color = 'blue';
                        socket.emit('mt_start', { lineNumber: index });
                        break;
                    case 1:
                        this.style.color = 'blue';
                        socket.emit('select_predicate', { paneId: paneId, lineNumber: index });
                        break;
                }
            }
            if (paneId === 'targetZone') {
                switch (mmode) {
                    case 1:
                        this.style.color = 'blue';
                        socket.emit('select_predicate', { paneId: paneId, lineNumber: index });
                        break;
                }
            }
            break;
        case 4:
            switch (rmode) {
                case 0:
                    event.target.blur();
                    if (paneId === 'hypothesisZone') {
                        this.style.color = 'blue';
                        socket.emit('rewrite_start', { lineNumber: index });
                    }
                break;
            }
    }
}

function handleBlur(event) {
    var parentPane = this.parentElement;
    var divsArray = Array.from(parentPane.querySelectorAll('div'));
    var index = divsArray.indexOf(this); // Find the index of the current div
    var pane = parentPane.id;
    switch (mode) {
        case 0:
            if (!isUpdatingContent) {
                updateDiv(event.target)
            }
    }
}

function unselect() {
    // unselect the text in all contenteditable divs
    var editableDivs = document.querySelectorAll('#leftPane .editablePane div');

    editableDivs.forEach(function(div) {
        div.style.color = 'black';
    });
}

function noEdit() {
    // unselect the text in all contenteditable divs
    var editableDivs = document.querySelectorAll('#leftPane .editablePane div');

    editableDivs.forEach(function(div) {
        div.style.contenteditable = 'false';
    });
}

function allowEdit() {
    // unselect the text in all contenteditable divs
    var editableDivs = document.querySelectorAll('#leftPane .editablePane div');

    editableDivs.forEach(function(div) {
        div.style.contenteditable = 'true';
    });
}

// Function to handle user input in editable panes
function sendLineToPython(paneId, lineNumber, text) {
    socket.emit('send_line', { paneId: paneId, lineNumber: lineNumber, text: text });
}

function startTheoremProving() {
    switch_mode(1);
    socket.emit('start')
}

function modusPonens() {
    updateStatus("Select implication")
    switch_mode(2);
    mmode = 0;
}

function modusTollens() {
    updateStatus("Select implication")
    switch_mode(3);
    mmode = 0;
}

function rewriteFormula() {
    updateStatus("Select equality")
    switch_mode(4);
    rmode = 0;
}

function startAutomation() {
    console.log("automation started");
    switch_mode(6);
    socket.emit('run_automation');
}

function clearTableau() {
    // Ask the user for confirmation
    var userConfirmed = confirm("Do you really want to clear the tableau?");

    if (userConfirmed) {
        // User clicked 'Yes', send a message to the Python server
        socket.emit('clear_tableau'); // Clear the tableau on the Python side
        clearPanes() // Clear the three panes in the interface
        isUpdatingContent = false
        isEditError = false
        error_line = -1;
        unselect();
        switch_mode(0);
    }
}

function clearPanes() {
    var panes = document.querySelectorAll('.editablePane');

    panes.forEach(pane => {
        // Remove all but the first div
        while (pane.children.length > 1) {
            pane.removeChild(pane.lastChild);
        }

        // Clear the text of the remaining div
        pane.children[0].innerText = '';
    });
}

function isTableauEmpty() {
    // Select all panes in the tableau
    var panes = document.querySelectorAll('.editablePane');
    
    // Iterate over each pane and check conditions
    for (var i = 0; i < panes.length; i++) {
        var divs = panes[i].querySelectorAll('div');

        // Check if there is exactly one div and its text content is empty
        if (divs.length !== 1 || divs[0].innerText.trim() !== '') {
            return false; // Tableau is not empty
        }
    }

    return true; // Tableau is empty if all panes pass the check
}

function setupEditableDivListeners() {
    document.querySelectorAll('.editablePane div').forEach(div => {
        div.addEventListener('keydown', handleKeyPress);
        div.addEventListener('focus', handleFocus);
        div.addEventListener('blur', handleBlur);
        div.addEventListener('mouseup', getSelectedText);
    });
}

window.onload = function() {
        socket.emit('clear_tableau'); // Clear the tableau on the Python side
        clearPanes() // Clear the three panes in the interface
        isUpdatingContent = false
        isEditError = false
        error_line = -1;
        unselect();
        switch_mode(0);
        // Assuming the text edit div has contenteditable attribute
        var textEditDiv = document.querySelector('.editablePane div[contenteditable="true"]');
        var quantifierZone = document.getElementById('quantifierZone');

        if (textEditDiv && quantifierZone) {
            // Get the height of the text edit div
            var height = textEditDiv.offsetHeight;

            // Set the height of the quantifier zone
            quantifierZone.style.height = height + 'px';
        }
        setupEditableDivListeners()
    };

socket.on('connect', function() {
    console.log("Successfully connected to WebSocket server.");
});

function updateDiv(lineDiv) {
    var pane = lineDiv.parentElement;
    var lineNumber = Array.from(pane.children).indexOf(lineDiv);
    var text = lineDiv.innerText;
    sendLineToPython(pane.id, lineNumber, text);
}

function fetchAndFillContent(divElement, lineNumber) {
    var paneId = divElement.parentElement.id;
    isUpdatingContent = true;
    divElement.blur(); // Blur div temporarily to prevent editing
    // Send a request to the server to get content for this line
    socket.emit('fetch_line_content', { paneId: paneId, lineNumber: lineNumber });
}

socket.on('fill_line_content', function(data) {
    var pane = document.getElementById(data.paneId);
    if (pane) {
        var divs = pane.querySelectorAll('div');
        if (data.lineNumber < divs.length) {
            var targetDiv = divs[data.lineNumber];
            targetDiv.innerText = data.content;
            targetDiv.focus(); // Set focus to the updated div
            isUpdatingContent = false;
            isEditError = false;
        }
    }
});

// Handling responses from the server
socket.on('update_line', function(data) {
    console.log("update_line data:", data);
    if (data.lineNumber === error_line) {
        error_line = -1; // clear error
    }
    isEditError = false
    isUpdatingContent = false
    var pane = document.getElementById(data.paneId);
    var lineDivs = pane.querySelectorAll('div'); // Select only div elements
    if (data.lineNumber < lineDivs.length) {
        lineDivs[data.lineNumber].innerText = data.updatedText;
    }
    // Check if the updated line is the last line in the pane
    if (data.lineNumber === lineDivs.length - 1 && data.paneId !== 'quantifierZone') {
        addNewLineToPane(data.paneId);
    }
});

function handleKeyPress(event) {
    if (mode === 0 && event.key === 'Enter') {
        event.preventDefault(); // Prevents default Enter key behavior (new line)
        isUpdatingContent = false
        event.target.blur();
    }
}

function cancel() {
    // cancel move
    updateStatus('')
    unselect(); // clear any selected hypotheses/targets
    switch_mode(1);
}    

socket.on('error', function(data) {
    errorMessage = data.msg
    restart = data.restart
    updateStatus(''); // clear any status message
    unselect(); // clear any selected hypotheses/targets
    console.log("Error received:", errorMessage);  // Add this line for debugging
    if (restart === true) {
        switch_mode(0);
        unselect();
    }
    if (mode > 0) {
        switch_mode(1);
    }
    alert(errorMessage);
});

socket.on('done', function() {
    updateStatus(''); // clear any status message
    unselect(); // clear any selected hypotheses/targets
    switch_mode(-1);
    alert('All targets proved!');
});

socket.on('not_done', function() {
    updateStatus(''); // clear any status message
    unselect(); // clear any selected hypotheses/targets
    switch_mode(1);
    alert('Unable to prove theorem');
});

socket.on('edit_error', function(data) {
    console.log("Error received:", data.msg);  // Add this line for debugging
    isUpdatingContent = true;
    if (!isEditError) {
        if (error_line !== data.lineNumber) { // ensure error issued only once
            alert(data.msg);
        }
    }
    error_line = data.lineNumber;
    isUpdatingContent = false;
    isEditError = true;
    var pane = document.getElementById(data.paneId);
    var lineDivs = pane.querySelectorAll('div'); // Select only div elements
    lineDivs[data.lineNumber].focus();
});

// Function to add a new editable line to a pane
function addNewLineToPane(paneId) {
    var pane = document.getElementById(paneId);
    var newLine = document.createElement('div');
    newLine.contentEditable = true;
    newLine.addEventListener('keydown', handleKeyPress);
    newLine.addEventListener('focus', handleFocus);
    newLine.addEventListener('blur', handleBlur);
    newLine.addEventListener('mouseup', getSelectedText);
    pane.appendChild(newLine);
}

function loadTableau() {
    if (isTableauEmpty()) {
        document.getElementById('overlay').style.display = 'block';
        document.getElementById('popup').style.display = 'block';
        updateDropdown(); // Initial population of the dropdown
    } else
    {
        alert("Tableau must be cleared first.")
    }
}

function importTheorem() {
    document.getElementById('overlay').style.display = 'block';
    document.getElementById('popup').style.display = 'block';
    switch_mode(5);
    updateDropdown(); // Initial population of the dropdown
}

function updateDropdown() {
    var tags = document.getElementById('tagsInput').value;
    var letter = document.getElementById('letterInput').value;

    socket.emit('request_library_filter', { tags: tags, letter: letter });
}

socket.on('update_dropdown', function(data) {
    var dropdown = document.getElementById('dropdown');
    dropdown.innerHTML = ''; // Clear existing options

    data.strings.forEach(function(string) {
        var option = document.createElement('option');
        option.value = string;
        option.text = string;
        dropdown.appendChild(option);
    });
});

function closePopup() {
    document.getElementById('overlay').style.display = 'none';
    document.getElementById('popup').style.display = 'none';
}

function loadTheorem() {
    var dropdown = document.getElementById('dropdown');
    var string = dropdown.value; // Get the selected value from the dropdown

    if (string) {
        switch (mode) {
            case 0:
                socket.emit('library_load', { selectedString: string });
                break
            case 5:
                socket.emit('library_import', { selectedString: string });
                break
            
        }
        closePopup();
    }
}

function cancelLoad() {
    closePopup();
    updateStatus('');
    unselect();
    if (mode > 0) {
        switch_mode(1);
    }
}

socket.on('update_dirty', function(data) {
    dirtytxt0 = data.dirtytxt0
    dirty1 = data.dirty1;
    dirtytxt1 = data.dirtytxt1;
    dirty2 = data.dirty2;
    dirtytxt2 = data.dirtytxt2;
    reset_mode = data.reset_mode
    unselect();
    if (reset_mode && mode > 0) {
        switch_mode(1);
    }
    updateStatus('');
    var pane = document.getElementById('quantifierZone');
    var lineDivs = pane.querySelectorAll('div'); // Select only div elements
    lineDivs[0].innerText = data.dirtytxt0
    pane = document.getElementById('hypothesisZone');
    lineDivs = pane.querySelectorAll('div'); // Select only div elements
    for (var i = 0; i < dirty1.length; i++) {
        j = dirty1[i]
        if (j >= lineDivs.length - 1) {
            addNewLineToPane('hypothesisZone');
            lineDivs = pane.querySelectorAll('div');
        };
        lineDivs[j].innerText = dirtytxt1[i]
    };
    pane = document.getElementById('targetZone');
    lineDivs = pane.querySelectorAll('div'); // Select only div elements
    for (var i = 0; i < dirty2.length; i++) {
        j = dirty2[i]
        if (j >= lineDivs.length - 1) {
            addNewLineToPane('targetZone');
            lineDivs = pane.querySelectorAll('div');
        };
        lineDivs[j].innerText = dirtytxt2[i]
    };
});

socket.on('get_predicate', function(num) {
    mmode = 1;
    if (num === 1) {
        updateStatus('Select predicate')
    } else {
        updateStatus('Select predicate'+num)
    }
});

socket.on('get_selection', function() {
    rmode = 1;
    updateStatus('Select expression to rewrite')
});

function getSelectedText(event) {
    if (mode === 4 && rmode === 1) {
        var selection = window.getSelection();
    
        if (selection.rangeCount > 0) {
            var div = event.target
            var parentPane = div.parentElement;
            var divsArray = Array.from(parentPane.querySelectorAll('div'));
            var index = divsArray.indexOf(div);
            var paneId = parentPane.id;

            var range = selection.getRangeAt(0);
            var selectedText = range.toString();

            var divContent = div.innerText;
            var start = range.startOffset;
            var end = range.endOffset;

            if (start !== end) {
                console.log('Selected text:', selectedText);
                console.log('Start index:', start, 'End index:', end);

                socket.emit('rewrite_selection', { paneId: paneId, lineNumber: index, start: start, end: end });
            }
        }
    }
}