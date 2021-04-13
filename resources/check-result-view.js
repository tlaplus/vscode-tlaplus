/* eslint-disable no-undef */
const vscode = acquireVsCodeApi();

const VAL_COL = ['val-col'];
const changeHints = {
    A: 'This item has been added since the previous state',
    M: 'This item has been modified since the previous state',
    D: 'This item has been deleted since the previous state'
};

let curState = vscode.getState() || {
    settings: {
        showUnmodified: true,   // Whether or not show error trace items whose values were not modified
        errorTraceFilter: '',   // Search string for filtering error trace items
        errorIndex: 0           // Index of the error whose trace is displayed at the moment
    }
};
let findChangeTimer;

initialize();

function initialize() {
    if (curState) {
        displayCheckResult(curState);
    }

    // Receives data from the extension.
    window.addEventListener('message', (event) => {
        const newState = {
            checkResult: event.data.checkResult,
            settings: curState.settings
        };
        curState = newState;
        displayCheckResult(newState);
        vscode.setState(newState);
    });

    const errTraceFilter = document.getElementById('error-trace-filter');
    errTraceFilter.value = curState.settings.errorTraceFilter;
    errTraceFilter.onkeydown = (e) => handleErrorTraceFilterChange(e.target.value);
    errTraceFilter.oninput = (e) => handleErrorTraceFilterChange(e.target.value);

    syncHideShowUnmodifiedText(curState.settings.showUnmodified);
    notifyInitialized();
}

function handleErrorTraceFilterChange(filterText) {
    clearTimeout(findChangeTimer);
    findChangeTimer = setTimeout(() => {
        curState.settings.errorTraceFilter = filterText;
        displayErrorTrace(curState.checkResult.errors, curState.settings);
        vscode.setState(curState);
    }, 500);
}

function displayCheckResult(state) {
    const res = state.checkResult;
    if (!res) {
        return;
    }
    displayStatus(res);
    displaySpecFiles(res.specFiles);
    displayStatesStat(res.initialStatesStat);
    displayCoverage(res.coverageStat);
    displayMessages(res.warnings, 'warnings', 'warnings-list', false);
    displayMessages(res.errors, 'errors', 'errors-list', res.errors.length > 1);
    displayErrorTrace(res.errors, state.settings);
    displayOutput(res.outputLines);
}

function notifyInitialized() {
    vscode.postMessage({
        command: 'init'
    });
}

function stopProcess() {
    vscode.postMessage({
        command: 'stop'
    });
}

function runCheckAgain() {
    vscode.postMessage({
        command: 'runAgain'
    });
}

function showTlcOutput() {
    vscode.postMessage({
        command: 'showTlcOutput'
    });
}

function showInfoMessage(text) {
    vscode.postMessage({
        command: 'showInfoMessage',
        text: text
    });
}

function showVariableValue(id) {
    vscode.postMessage({
        command: 'showVariableValue',
        valueId: id
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

function displayStatus(result) {
    const stillRunning = result.state === 'R';
    displayStatusHeader(result.showFullOutput, stillRunning);
    const elTimeStart = document.getElementById('time-start');
    const elTimeEnd = document.getElementById('time-end');
    const elState = document.getElementById('check-state');
    const elStatusDetails = document.getElementById('check-status-details');
    const elCmdStopWrapper = document.getElementById('cmd-stop-wrapper');
    elTimeStart.innerText = result.startDateTimeStr;
    elTimeEnd.innerText = result.endDateTimeStr;
    elState.innerText = result.stateName;
    elState.classList = [`state-${result.state}`];
    if (stillRunning) {
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

function displaySpecFiles(specFiles) {
    const elSpecFiles = document.getElementById('spec-files');
    if (specFiles) {
        const elTlaFileName = document.getElementById('tla-file-name');
        const elCfgFileName = document.getElementById('cfg-file-name');
        elTlaFileName.innerText = specFiles.tlaFileName;
        elCfgFileName.innerText = specFiles.cfgFileName;
        elSpecFiles.classList.remove('hidden');
    } else {
        elSpecFiles.classList.add('hidden');
    }
}

function displayStatusHeader(showActions, stillRunning) {
    const elActions = document.getElementById('actions');
    const elShowOutput = document.getElementById('act-show-output');
    const elRunAgain = document.getElementById('act-run-again');
    if (showActions) {
        elActions.classList.remove('hidden');
        elShowOutput.onclick = () => showTlcOutput();
    } else {
        elActions.classList.add('hidden');
        delete elShowOutput.onclick;
    }
    if (stillRunning) {
        delete elRunAgain.onclick;
        elRunAgain.classList.add('hidden');
    } else {
        elRunAgain.onclick = () => runCheckAgain();
        elRunAgain.classList.remove('hidden');
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
    const elCoverage = document.getElementById('coverage');
    if (stat.length === 0) {
        elCoverage.classList.add('hidden');
        return;
    }
    elCoverage.classList.remove('hidden');
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

function displayMessages(infos, wrapperId, listId, errorTraceLinks) {
    const elWrapper = document.getElementById(wrapperId);
    const elList = document.getElementById(listId);
    removeAllChildren(elList);
    if (!infos || infos.length === 0) {
        elWrapper.classList.add('hidden');
        return;
    }
    elWrapper.classList.remove('hidden');
    let idx = 0;
    for (const info of infos) {
        const elMessage = document.createElement('p');
        elMessage.classList = ['message'];
        info.lines.forEach((line) => displayMessageLine(elMessage, line));
        if (errorTraceLinks && info.errorTrace && info.errorTrace.length > 0) {
            const elLink = document.createElement('a');
            elLink.setAttribute('href', '#');
            elLink.innerText = 'Show error trace';
            const errIdx = idx;
            elLink.onclick = (e) => setErrorIndex(e, errIdx);
            elMessage.appendChild(elLink);
        }
        elList.appendChild(elMessage);
        idx += 1;
    }
}

function displayMessageLine(elParent, line) {
    const elLine = document.createElement('p');
    elLine.classList = ['message-line'];
    line.spans.forEach((span) => {
        if (span.type === 'SL') {
            const elLink = appendTextChild(elLine, 'a', span.text);
            elLink.setAttribute('href', '#');
            elLink.onclick = (e) => openFile(e, span.filePath, span.location);
        } else {
            appendTextChild(elLine, 'span', span.text);
        }
    });
    elParent.appendChild(elLine);
}

function displayErrorTrace(errors, settings) {
    const filterItems = parseFilter(settings.errorTraceFilter);
    const elErrorTrace = document.getElementById('error-trace');
    const elErrorTraceItems = document.getElementById('error-trace-items');
    removeAllChildren(elErrorTraceItems);
    adjustErrorIndex(errors, settings);
    if (!errors || errors.length === 0 || settings.errorIndex < 0) {
        elErrorTrace.classList.add('hidden');
        return;
    }
    const trace = errors[settings.errorIndex].errorTrace;
    document.getElementById('error-trace-idx').innerText = errors.length > 1 ? `#${settings.errorIndex + 1}` : '';
    const elShowHideSwitch = document.getElementById('unmodified-switch');
    elShowHideSwitch.onclick = (e) => setShowUnmodified(e, !settings.showUnmodified);
    elErrorTrace.classList.remove('hidden');
    trace.forEach((item) => displayErrorTraceItem(elErrorTraceItems, item, settings.showUnmodified, filterItems));
    const expNodes = document.getElementsByClassName('tree-expandable');
    for (const node of expNodes) {
        node.onclick = (e) => {
            const elName = e.target;
            elName.parentElement.parentElement.querySelector('.tree-nodes').classList.toggle('shown');
            elName.classList.toggle('tree-expandable-down');
        };
    }
}

function displayErrorTraceItem(elErrorTraceVars, item, showUnmodified, filterItems) {
    const eShowUnmodified = showUnmodified || item.num === 1;
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
    item.variables.items
        .filter((v) => checkFilter(v.key, filterItems))
        .forEach((v) => displayValue(elVarList, v, eShowUnmodified));
    elItem.appendChild(elVarList);
    elErrorTraceVars.appendChild(elItem);
}

function displayValue(elParent, value, showUnmodified) {
    if (!showUnmodified && value.changeType === 'N') {
        return;
    }
    const elVar = document.createElement('li');
    const elVarValueBlock = document.createElement('div');
    elVarValueBlock.classList.add('var-block');
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
    elVarValueBlock.appendChild(renderValueMenu(value));
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
        elVarChange.classList.add(`change-marker-${value.changeType}`);
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

function renderValueMenu(value) {
    const elMenu = document.createElement('div');
    elMenu.classList.add('var-menu');
    if (value.changeType !== 'D') {
        // "Display value" item
        const elDislplay = document.createElement('div');
        elDislplay.classList.add('var-button');
        elDislplay.classList.add('var-button-display');
        elDislplay.innerHTML = '&nbsp;';
        elDislplay.setAttribute('title', 'Dislpay value');
        elDislplay.onclick = () => showVariableValue(value.id);
        elMenu.appendChild(elDislplay);
    }
    // "Copy to clipboard" item
    const elCopy = document.createElement('div');
    elCopy.classList.add('var-button');
    elCopy.classList.add('var-button-copy');
    elCopy.innerHTML = '&nbsp;';
    elCopy.setAttribute('title', 'Copy value to clipboard');
    elCopy.onclick = () => {
        copyValueToClipboard(value);
        showInfoMessage('Value has been copied to clipboard');
    };
    elMenu.appendChild(elCopy);
    return elMenu;
}

function copyValueToClipboard(value) {
    const el = document.createElement('textarea');
    el.value = value.str;
    document.body.appendChild(el);
    el.select();
    document.execCommand('copy');
    document.body.removeChild(el);
}

function num(n) {
    if (n < 1000) {
        return String(n);
    }
    const parts = [];
    const sign = n < 0 ? '-' : '';
    let en = Math.abs(n);
    while (en > 0) {
        const r = en % 1000;
        en = (en - r) / 1000;
        const rStr = en > 0 ? lpadN(r) : String(r);
        parts.push(rStr);
    }
    const revParts = parts.reverse().join(' ');
    return sign + revParts;
}

function lpadN(n) {
    if (n === 0) {
        return '000';
    } else if (n < 10) {
        return `00${n}`;
    } else if (n < 100) {
        return `0${n}`;
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

function setErrorIndex(event, errorIndex) {
    event.preventDefault();
    event.stopPropagation();
    curState.settings.errorIndex = errorIndex;
    displayErrorTrace(curState.checkResult.errors, curState.settings);
    vscode.setState(curState);
    document.getElementById('error-trace').scrollIntoView();
}

function setShowUnmodified(event, show) {
    event.preventDefault();
    event.stopPropagation();
    event.target.blur();
    syncHideShowUnmodifiedText(show);
    curState.settings.showUnmodified = show;
    displayErrorTrace(curState.checkResult.errors, curState.settings);
    vscode.setState(curState);
}

function syncHideShowUnmodifiedText(show) {
    document.getElementById('unmodified-switch').innerText = show ? 'Hide unmodified' : 'Show unmodified';
}

function parseFilter(filterText) {
    if (!filterText) {
        return [];
    }
    return filterText.trim().split(/\s|,/g).filter(p => p !== '').map(p => p.toLowerCase());
}

function checkFilter(str, filterItems) {
    if (filterItems.length === 0) {
        return true;
    }
    const eKey = str.toLowerCase();
    for (const fi of filterItems) {
        if (eKey.indexOf(fi) >= 0) {
            return true;
        }
    }
    return false;
}

function adjustErrorIndex(errors, settings) {
    if (!errors || errors.length === 0) {
        settings.errorIndex = -1;
        return;
    }
    if (settings.errorIndex >= 0 && settings.errorIndex < errors.length) {
        return;
    }
    // Search for the first error with error trace
    settings.errorIndex = -1;
    for (let i = 0; i < errors.length; i++) {
        if (errors[i].errorTrace && errors[i].errorTrace.length > 0) {
            settings.errorIndex = i;
            break;
        }
    }
}
