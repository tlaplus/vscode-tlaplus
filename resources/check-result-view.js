const vscode = acquireVsCodeApi();

const VAL_COL = ['val-col'];
const changeHints = {
    A: 'This item has been added since the previous state',
    M: 'This item has been modified since the previous state',
    D: 'This item has been deleted since the previous state'
};

let curState = vscode.getState() || { settings: { showUnmodified: true } };

if (curState) {
    displayCheckResult(curState);
}

function displayCheckResult(state) {
    const res = state.checkResult;
    if (!res) {
        return;
    }
    displayStatus(res);
    displayStatesStat(res.initialStatesStat);
    displayCoverage(res.coverageStat);
    displayWarnings(res.warnings);
    displayErrors(res.errors);
    displayErrorTrace(res.errorTrace, state.settings.showUnmodified);
    displayOutput(res.outputLines);
}

function stopProcess() {
    vscode.postMessage({
        command: 'stop'
    });
}

function showTlcOutput() {
    vscode.postMessage({
        command: 'showTlcOutput'
    });
}

function openFile(event, filePath, location) {
    event.preventDefault();
    event.stopPropagation();
    vscode.postMessage({
        command: 'openFile',
        filePath,
        location
    });
}

/**
 * Receives data from the extension.
 */
window.addEventListener('message', (event) => {
    const newState = {
        checkResult: event.data.checkResult,
        settings: curState.settings
    };
    curState = newState;
    displayCheckResult(newState);
    vscode.setState(newState);
});

function displayStatus(result) {
    displayStatusHeader(result.showFullOutput);
    const elTimeStart = document.getElementById('time-start');
    const elTimeEnd = document.getElementById('time-end');
    const elState = document.getElementById('check-state');
    const elStatusDetails = document.getElementById('check-status-details');
    const elCmdStopWrapper = document.getElementById('cmd-stop-wrapper');
    elTimeStart.innerText = result.startDateTimeStr;
    elTimeEnd.innerText = result.endDateTimeStr;
    elState.innerText = result.stateName;
    elState.classList = ['state-' + result.state];
    if (result.state === 'R') {
        // Still running
        elCmdStopWrapper.classList.remove('hidden');
        elCmdStopWrapper.onclick = () => stopProcess();
    } else {
        elCmdStopWrapper.classList.add('hidden');
        delete elCmdStopWrapper.onclick;
    }
    if (result.statusDetails) {
        elStatusDetails.classList.remove('hidden');
        elStatusDetails.innerText = result.statusDetails;
    } else {
        elStatusDetails.classList.add('hidden');
    }
}

function displayStatusHeader(showFullOutput) {
    const elOutputLink = document.getElementById('output-link');
    if (showFullOutput) {
        elOutputLink.classList.remove('hidden');
        elOutputLink.onclick = () => showTlcOutput();
    } else {
        elOutputLink.classList.add('hidden');
        delete elOutputLink.onclick;
    }
}

function displayStatesStat(stat) {
    const elStatesStat = document.getElementById('states-stat');
    removeAllChildren(elStatesStat);
    stat.forEach((item) => {
        const elRow = document.createElement('tr');
        appendTextChild(elRow, 'td', item.timeStamp, VAL_COL);
        appendTextChild(elRow, 'td', num(item.diameter), VAL_COL);
        appendTextChild(elRow, 'td', num(item.total), VAL_COL);
        appendTextChild(elRow, 'td', num(item.distinct), VAL_COL);
        appendTextChild(elRow, 'td', num(item.queueSize), VAL_COL);
        elStatesStat.appendChild(elRow);
    });
}

function displayCoverage(stat) {
    const elCoverageStat = document.getElementById('coverage-stat');
    removeAllChildren(elCoverageStat);
    stat.forEach((item) => {
        const elRow = document.createElement('tr');
        if (item.total === 0) {
            elRow.classList.add('coverage-zero');
            elRow.setAttribute('title', 'This action has never been used to compute successor states');
        }
        appendTextChild(elRow, 'td', item.module);
        appendCodeLinkChild(elRow, 'td', item.action, item.filePath, item.range[0]);
        appendTextChild(elRow, 'td', num(item.total), VAL_COL);
        appendTextChild(elRow, 'td', num(item.distinct), VAL_COL);
        elCoverageStat.appendChild(elRow);
    });
}

function displayWarnings(warnings) {
    displayMessages(warnings, 'warnings', 'warnings-list');
}

function displayErrors(errors) {
    displayMessages(errors, 'errors', 'errors-list');
}

function displayMessages(messages, wrapperId, listId) {
    const elWrapper = document.getElementById(wrapperId);
    const elList = document.getElementById(listId);
    removeAllChildren(elList);
    if (!messages || messages.length === 0) {
        elWrapper.classList.add('hidden');
        return;
    }
    elWrapper.classList.remove('hidden');
    messages.forEach((msg) => {
        const elMessage = document.createElement('p');
        elMessage.classList = ['message'];
        msg.forEach((line) => displayMessageLine(elMessage, line));
        elList.appendChild(elMessage);
    });
}

function displayMessageLine(elParent, line) {
    const elLine = document.createElement('p');
    elLine.classList = ['message-line'];
    line.spans.forEach((span) => {
        if (span.type === 'SL') {
            const elLink = appendTextChild(elLine, 'a', span.text);
            elLink.setAttribute('href', '#');
            elLink.onclick = (e) => openFile(e, span.filePath, span.location)
        } else {
            appendTextChild(elLine, 'span', span.text);
        }
    });
    elParent.appendChild(elLine);
}

function displayErrorTrace(trace, showUnmodified) {
    const elErrorTrace = document.getElementById('error-trace');
    const elErrorTraceItems = document.getElementById('error-trace-items');
    removeAllChildren(elErrorTraceItems);
    if (!trace || trace.length === 0) {
        elErrorTrace.classList.add('hidden');
        return;
    }
    const elShowHideSwitch = document.getElementById('unmodified-switch');
    elShowHideSwitch.onclick = (e) => setShowUnmodified(e, !showUnmodified);
    elErrorTrace.classList.remove('hidden');
    trace.forEach((item) => displayErrorTraceItem(elErrorTraceItems, item, showUnmodified));
    const expNodes = document.getElementsByClassName('tree-expandable');
    for (const node of expNodes) {
        node.onclick = (e) => {
            const elName = e.target;
            elName.parentElement.parentElement.querySelector('.tree-nodes').classList.toggle('shown');
            elName.classList.toggle('tree-expandable-down');
        };
    }
}

function displayErrorTraceItem(elErrorTraceVars, item, showUnmodified) {
    let eShowUnmodified = showUnmodified || item.num === 1;
    const elItem = document.createElement('li');
    const elItemBlock = document.createElement('div');
    elItemBlock.classList.add('error-trace-item-block');
    const elHeader = document.createElement('div');
    elHeader.classList.add('tree-node');
    elHeader.classList.add('tree-expandable');
    elHeader.classList.add('tree-expandable-down');
    elHeader.classList.add('error-trace-item-title');
    elHeader.innerText = `${item.num}: ${item.title} `;
    if (item.filePath && item.range) {
        appendCodeLinkChild(elHeader, 'span', '>>', item.filePath, item.range[0]);
    }
    elItemBlock.appendChild(elHeader);
    elItem.appendChild(elItemBlock);
    const elVarList = document.createElement('ul');
    elVarList.classList.add('tree-nodes');
    elVarList.classList.add('hidden');
    elVarList.classList.add('shown');
    item.variables.items.forEach((v) => displayValue(elVarList, v, eShowUnmodified));
    elItem.appendChild(elVarList);
    elErrorTraceVars.appendChild(elItem);
}

function displayValue(elParent, value, showUnmodified) {
    if (!showUnmodified && value.changeType === 'N') {
        return;
    }
    const elVar = document.createElement('li');
    const elVarValueBlock = document.createElement('div');
    const elVarKey = renderValueTitle(value);
    elVarValueBlock.appendChild(elVarKey);
    const elVarValue = document.createElement('div');
    elVarValue.classList.add('var-value');
    elVarValue.innerText = value.str;
    if (value.changeType === 'D') {
        elVarValue.classList.add('value-deleted');
    }
    elVarValueBlock.appendChild(elVarValue);
    elVar.appendChild(elVarValueBlock);
    if (value.items && (value.items.length > 1 || value.items.length === 1 && value.expandSingle)) {
        elVarKey.classList.add('tree-expandable');
        const elSubList = document.createElement('ul');
        elSubList.classList.add('tree-nodes');
        elSubList.classList.add('hidden');
        value.items.forEach((it) => displayValue(elSubList, it, showUnmodified));
        if (value.deletedItems) {
            value.deletedItems.forEach((dit) => displayValue(elSubList, dit, showUnmodified));
        }
        elVar.appendChild(elSubList);
    }
    elParent.appendChild(elVar);
}

function renderValueTitle(value) {
    const elVarTitle = document.createElement('div');
    elVarTitle.classList.add('var-name');
    elVarTitle.classList.add('tree-node');
    const elVarKey = document.createElement('span');
    elVarKey.innerText = value.key;
    if (value.changeType === 'D') {
        elVarKey.classList.add('value-deleted');
    }
    elVarTitle.appendChild(elVarKey);
    if (value.items) {
        const elVarSize = document.createElement('span');
        elVarSize.classList.add('var-size');
        elVarSize.innerText = `(${value.items.length})`;
        elVarSize.setAttribute('title', 'Size of the collection');
        elVarTitle.appendChild(elVarSize);
    }
    const elVarChange = document.createElement('span');
    if (value.changeType !== 'N') {
        elVarChange.classList.add('change-marker');
        elVarChange.classList.add('change-marker-' + value.changeType);
        elVarChange.innerText = value.changeType;
        elVarChange.setAttribute('title', changeHints[value.changeType]);
    }
    elVarTitle.appendChild(elVarChange);
    return elVarTitle;
}

function displayOutput(lines) {
    const elOutput = document.getElementById('output');
    const elLines = document.getElementById('output-lines');
    removeAllChildren(elLines);
    if (!lines || lines.length === 0) {
        elOutput.classList.add('hidden');
        return;
    }
    elOutput.classList.remove('hidden');
    lines.forEach((line) => {
        const elLine = document.createElement('p');
        elLine.classList.add('output-line');
        let elText;
        if (line.count === 1) {
            elText = elLine;
        } else {
            elText = document.createElement('span');
            elLine.appendChild(elText);
            const elCount = appendTextChild(elLine, 'span', String(line.count), ['output-line-count']);
            elCount.setAttribute('title', 'Number of consecutive occurrences');
        }
        elText.innerText = line.text;
        elLines.appendChild(elLine);
    });
}

function num(n) {
    if (n < 1000) {
        return n;
    }
    const parts = [];
    const sign = n < 0 ? '-' : '';
    let en = Math.abs(n);
    while (en > 0) {
        const r = en % 1000;
        en = (en - r) / 1000;
        let rStr = en > 0 ? lpadN(r) : String(r);
        parts.push(rStr);
    }
    return sign + parts.reverse().join(' ');
}

function lpadN(n) {
    if (n === 0) {
        return '000';
    } else if (n < 10) {
        return '00' + n;
    } else if (n < 100) {
        return '0' + n;
    }
    return String(n);
}

function removeAllChildren(el) {
    while (el.lastChild) {
        el.removeChild(el.lastChild);
    }
}

function appendTextChild(elParent, tag, innerText, classes) {
    const el = document.createElement(tag);
    if (innerText) {
        el.innerText = innerText;
    }
    if (classes) {
        classes.forEach((c) => el.classList.add(c));
    }
    elParent.appendChild(el);
    return el;
}

function appendCodeLinkChild(elParent, tag, innerText, filePath, location, classes) {
    const el = document.createElement(tag);
    if (filePath && location) {
        const elLink = appendTextChild(el, 'a', innerText);
        elLink.onclick = (e) => openFile(e, filePath, location);
        elLink.setAttribute('href', '#');
    } else if (innerText) {
        el.innerText = innerText;
    }
    if (classes) {
        classes.forEach((c) => el.classList.add(c));
    }
    elParent.appendChild(el);
    return el;
}

function setShowUnmodified(event, show) {
    event.preventDefault();
    event.stopPropagation();
    event.target.blur();
    const elShowHideSwitch = document.getElementById('unmodified-switch');
    if (show) {
        elShowHideSwitch.innerText = 'Hide unmodified';
    } else {
        elShowHideSwitch.innerText = 'Show unmodified';
    }
    displayErrorTrace(curState.checkResult.errorTrace, show);
    curState.settings.showUnmodified = show;
    vscode.setState(curState);
}
