/**
 * The "client-side" JavaScript code for the model editor web view. Please observe the numerous TODO in
 *  comments below.
 */
const vscode = acquireVsCodeApi();

initialize();

function initialize() {
    window.addEventListener('message', (event) => {
        if (typeof event.data.modelConstants !== 'undefined') {
            populateModelConstants(event.data.modelConstants);
        } else if (typeof event.data.editors !== 'undefined') {
            populateOpenEditorsList(event.data.editors);
        }
    });

    const behaviorSpecSelectElement = document.getElementById("behavior-spec");
    behaviorSpecSelectElement.addEventListener("change", function() {
        const selectedBehavior = behaviorSpecSelectElement.options[behaviorSpecSelectElement.selectedIndex].value;
        const initNextDiv = document.getElementById("init-next-div");
        const temporalDiv = document.getElementById("temporal-div");

        if (selectedBehavior == "init-next") {
            initNextDiv.style.display = "block";
            temporalDiv.style.display = "none";
        } else if (selectedBehavior == "temporal") {
            initNextDiv.style.display = "none";
            temporalDiv.style.display = "block";
        } else {
            initNextDiv.style.display = "none";
            temporalDiv.style.display = "none";
        }

        validateModelEditorState();
    });

    wireKeyUpValidation("init-declaration");
    wireKeyUpValidation("next-declaration");
    wireKeyUpValidation("temporal-declaration");

    vscode.postMessage({
        command: 'getOpenEditors'
    });
}

// Invoked in response to extension -> view
function populateModelConstants(modelConstants) {
    const modelConstantsDiv = document.getElementById('model-constants-div');

    while (modelConstantsDiv.firstChild) {
        modelConstantsDiv.removeChild(modelConstantsDiv.lastChild);
    }

    modelConstants.forEach(function (modelConstant) {
        const divElement = document.createElement("div");
        divElement.classList.add("constant_definition");
        divElement.setAttribute("data-constant-name", modelConstant);
        divElement.appendChild(document.createTextNode(modelConstant + " →"));
        appendConstantSettingsDiv(divElement, modelConstant + "_");
        modelConstantsDiv.appendChild(divElement);
    });

    validateModelEditorState();
}

// Invoked in response to extension -> view
function populateOpenEditorsList(editorFilenames) {
    if (editorFilenames != null) {
        const editorSelectElement = document.getElementById('editor-chooser');

        editorSelectElement.appendChild(document.createElement("option"));
        editorFilenames.forEach(function (filename) {
            const option = document.createElement("option");
            let index = filename.lastIndexOf('/');
            if (index == -1) {
                index = filename.lastIndexOf("\\");
            }
            const name = document.createTextNode(filename.substring(index + 1));

            option.setAttribute("value", filename);
            option.appendChild(name);
            editorSelectElement.appendChild(option);
        });

        editorSelectElement.addEventListener("change", function() {
            const selectedFilename = editorSelectElement.options[editorSelectElement.selectedIndex].value;

            if (selectedFilename) {
                vscode.postMessage({
                    command: 'getModelConstants',
                    filename: selectedFilename
                });
            }
        });
    }
}

// Invoked from view user action
function startModelCheck() {
    const behaviorSpecSelectElement = document.getElementById("behavior-spec");
    const behaviorSpec = new Object();
    behaviorSpec.kind = behaviorSpecSelectElement.options[behaviorSpecSelectElement.selectedIndex].value;
    if (behaviorSpec.kind == "init-next") {
        behaviorSpec.init = document.getElementById("init-declaration").value.trim();
        behaviorSpec.next = document.getElementById("next-declaration").value.trim();
    } else if (behaviorSpec.kind == "temporal") {
        behaviorSpec.temporal = document.getElementById("temporal-declaration").value.trim();
    }

    const constants = new Array();
    const constantDivs = document.getElementsByClassName("constant_definition");
    for (let i = 0; i < constantDivs.length; i++) {
        const typeRadioElements = constantDivs[i].querySelectorAll("input[name='constant-type']");
        let selectedRadio = null;
        for (let j = 0; j < typeRadioElements.length; j++) {
            if (typeRadioElements[j].checked) {
                selectedRadio = typeRadioElements[j];
                break;
            }
        }

        const valueTextField = constantDivs[i].querySelector("input[type='text']");
        const constant = new Object();
        constant.name = constantDivs[i].getAttribute("data-constant-name");
        constant.type = selectedRadio.value;
        constant.value = valueTextField.value;
        // TODO symmetry set, Type need to be sent across

        constants.push(constant);
    }

    const editorSelectElement = document.getElementById('editor-chooser');
    vscode.postMessage({
        command: 'writeMCFiles',
        filename: editorSelectElement.options[editorSelectElement.selectedIndex].value,
        behaviorSpec: behaviorSpec,
        constants: constants
    });

    vscode.postMessage({
        command: 'startModelCheck',
        filename: editorSelectElement.options[editorSelectElement.selectedIndex].value
    });

    // In the correctly written version, we should wait for an ACK before hiding this element
    const modelCheckLinkElement = document.getElementById("action-start-model-check");
    modelCheckLinkElement.classList.add("hidden");
    delete modelCheckLinkElement.onclick;

    // TODO In the correctly written version, we should wait for an ACK before showing and arming this element
    const stopModelCheckLinkElement = document.getElementById("action-stop-model-check");
    stopModelCheckLinkElement.classList.remove("hidden");
    stopModelCheckLinkElement.onclick = () => stopModelCheck();
}

// Invoked from view user action
function stopModelCheck() {
    vscode.postMessage({
        command: 'stopModelCheck'
    });

    // TODO In the correctly written version, we should wait for an ACK before hiding this element
    const modelCheckLinkElement = document.getElementById("action-stop-model-check");
    modelCheckLinkElement.classList.add("hidden");
    delete modelCheckLinkElement.onclick;

    validateModelEditorState();
}

function wireKeyUpValidation(id) {
    const element = document.getElementById(id);
    element.onkeyup = () => validateModelEditorState();
}

function validateModelEditorState() {
    const editorSelectElement = document.getElementById('editor-chooser');
    const selectedFilename = editorSelectElement.options[editorSelectElement.selectedIndex].value;
    let canExecute = (selectedFilename && (selectedFilename.length > 0));

    if (canExecute) {
        const behaviorSpecSelectElement = document.getElementById("behavior-spec");
        const selectedBehavior = behaviorSpecSelectElement.options[behaviorSpecSelectElement.selectedIndex].value;
        if (selectedBehavior == "init-next") {
            const initDeclarationDiv = document.getElementById("init-declaration");
    
            if (initDeclarationDiv.value.trim().length > 0) {
                const nextDeclarationDiv = document.getElementById("next-declaration");
    
                canExecute = (nextDeclarationDiv.value.trim().length > 0);
            } else {
                canExecute = false;
            }
        } else if (selectedBehavior == "temporal") {
            const temporalDeclarationDiv = document.getElementById("temporal-declaration");
    
            canExecute = (temporalDeclarationDiv.value.trim().length > 0);
        }
    
        if (canExecute) {
            const constantTextFields = document.getElementsByClassName("constant_definition_textfield");
            for (let i = 0; i < constantTextFields.length; i++) {
                if (constantTextFields[i].value.trim().length == 0) {
                    canExecute = false;
                    break;
                }
            }
        }
    }

    const modelCheckLinkElement = document.getElementById("action-start-model-check");
    if (canExecute) {
        modelCheckLinkElement.classList.remove("hidden");
        modelCheckLinkElement.onclick = () => startModelCheck();
    } else {
        modelCheckLinkElement.classList.add("hidden");
        delete modelCheckLinkElement.onclick;
    }
}

function appendConstantSettingsDiv(divElement, idPrefix) {
    const textField = document.createElement("input");
    textField.setAttribute("type", "text");
    textField.setAttribute("id", idPrefix + "textfield");
    textField.classList.add('constant_definition_input');
    textField.classList.add('constant_definition_textfield');
    textField.onkeyup = () => validateModelEditorState();
    divElement.appendChild(textField);

    const ordinaryRadio = document.createElement("input");
    ordinaryRadio.setAttribute("type", "radio");
    ordinaryRadio.setAttribute("name", "constant-type");
    ordinaryRadio.setAttribute("value", "ordinary");
    ordinaryRadio.checked = true;
    ordinaryRadio.setAttribute("id", idPrefix + "ordinary-radio");
    ordinaryRadio.classList.add('constant_definition_input');
    divElement.appendChild(ordinaryRadio);
    const ordinaryLabel = document.createElement("label");
    ordinaryLabel.setAttribute("for", idPrefix + "ordinary-radio");
    ordinaryLabel.appendChild(document.createTextNode("ordinary assignment"));
    ordinaryLabel.classList.add('constant_definition_label');
    divElement.appendChild(ordinaryLabel);

    const modelValueRadio = document.createElement("input");
    modelValueRadio.setAttribute("type", "radio");
    modelValueRadio.setAttribute("name", "constant-type");
    modelValueRadio.setAttribute("value", "model-value");
    modelValueRadio.setAttribute("id", idPrefix + "model-value-radio");
    modelValueRadio.classList.add('constant_definition_input');
    divElement.appendChild(modelValueRadio);
    const modelValueLabel = document.createElement("label");
    modelValueLabel.setAttribute("for", idPrefix + "model-value-radio");
    modelValueLabel.appendChild(document.createTextNode("model value"));
    modelValueLabel.classList.add('constant_definition_label');
    divElement.appendChild(modelValueLabel);

    const setOfModelValuesRadio = document.createElement("input");
    setOfModelValuesRadio.setAttribute("type", "radio");
    setOfModelValuesRadio.setAttribute("name", "constant-type");
    setOfModelValuesRadio.setAttribute("value", "set-of-model-values");
    setOfModelValuesRadio.setAttribute("id", idPrefix + "set-of-model-values-radio");
    setOfModelValuesRadio.classList.add('constant_definition_input');
    divElement.appendChild(setOfModelValuesRadio);
    const setOfModelValuesLabel = document.createElement("label");
    setOfModelValuesLabel.setAttribute("for", idPrefix + "set-of-model-values-radio");
    setOfModelValuesLabel.appendChild(document.createTextNode("set of model values"));
    setOfModelValuesLabel.classList.add('constant_definition_label');
    divElement.appendChild(setOfModelValuesLabel);

    const symmetrySetCheckbox = document.createElement("input");
    symmetrySetCheckbox.setAttribute("type", "checkbox");
    symmetrySetCheckbox.setAttribute("value", "symmetry-set");
    symmetrySetCheckbox.setAttribute("id", idPrefix + "symmetry-set-checkbox");
    divElement.appendChild(symmetrySetCheckbox);
    const symmetrySetLabel = document.createElement("label");
    symmetrySetLabel.setAttribute("for", idPrefix + "symmetry-set-checkbox");
    symmetrySetLabel.appendChild(document.createTextNode("symmetry set"));
    divElement.appendChild(symmetrySetLabel);

    const typeCheckbox = document.createElement("input");
    typeCheckbox.setAttribute("type", "checkbox");
    typeCheckbox.setAttribute("value", "model-set-type");
    typeCheckbox.setAttribute("id", idPrefix + "model-set-type-checkbox");
    divElement.appendChild(typeCheckbox);
    const typeLabel = document.createElement("label");
    typeLabel.setAttribute("for", idPrefix + "model-set-type-checkbox");
    typeLabel.appendChild(document.createTextNode("Type"));
    divElement.appendChild(typeLabel);

    // TODO type combobox
    // TODO enable/disable logic on sym set and type

    /*
constant name -> _value_textfield_  ( ) ordinary assignment  ( ) model value  ( ) set of model values [ ] symmetry set [ ] Type [A |v]
    */
}
