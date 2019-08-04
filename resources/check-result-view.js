const vscode = acquireVsCodeApi();

const changeHints = {
    A: 'This item has been added since the previous state',
    M: 'This item has been modified since the previous state',
    D: 'This item has been deleted since the previous state'
}

const prevState = vscode.getState();
if (prevState) {
    displayCheckResult(prevState);
}

function displayCheckResult(data) {
    const res = data.checkResult;
    displayStatus(res);
    displayStatesStat(res.initialStatesStat);
    displayCoverage(res.coverageStat);
    displayErrors(res.errors);
    displayErrorTrace(res.errorTrace, data);
    displayOutput(res.outputLines);
}

function stopProcess() {
    vscode.postMessage({
        command: 'stop'
    });
}

/**
 * Recieves data from the extension.
 */
window.addEventListener('message', event => {
    displayCheckResult(event.data);
    vscode.setState(event.data);
});

function displayStatus(result) {
    const elTimeStart = document.getElementById('time-start');
    const elTimeEnd = document.getElementById('time-end');
    const elState = document.getElementById('check-state');
    const elStatusDetails = document.getElementById('check-status-details');
    const elCmdStop = document.getElementById('cmd-stop');
    elTimeStart.textContent = result.startDateTimeStr;
    elTimeEnd.textContent = result.endDateTimeStr;
    elState.textContent = result.stateName;
    elState.classList = ['state-' + result.state];
    if (result.state === 'R') {
        // Still running
        elCmdStop.classList.remove('hidden');
    } else {
        elCmdStop.classList.add('hidden');
    }
    if (result.statusDetails) {
        elStatusDetails.classList.remove('hidden');
        elStatusDetails.textContent = result.statusDetails;
    } else {
        elStatusDetails.classList.add('hidden');
    }
}

function displayStatesStat(stat) {
    const elStatesStat = document.getElementById('states-stat');
    elStatesStat.innerHTML = stat
        .map(s => `<tr><td class="val-col">${s.timeStamp}</td><td class="val-col">${num(s.diameter)}</td><td class="val-col">${num(s.total)}</td><td class="val-col">${num(s.distinct)}</td><td class="val-col">${num(s.queueSize)}</td></tr>`)
        .join('');
}

function displayCoverage(stat) {
    const elCoverageStat = document.getElementById('coverage-stat');
    elCoverageStat.innerHTML = stat
        .map(s => `<tr><td>${s.module}</td><td>${s.action}</td><td class="val-col">${num(s.total)}</td><td class="val-col">${num(s.distinct)}</td></tr>`)
        .join('');
}

function displayErrors(errors) {
    const elErrors = document.getElementById('errors');
    const elErrorsList = document.getElementById('errors-list');
    removeAllChildren(elErrorsList);
    if (!errors || errors.length === 0) {
        elErrors.classList.add('hidden');
        return;
    }
    elErrors.classList.remove('hidden');
    errors.forEach(err => {
        const elError = document.createElement('p');
        elError.classList = ['error'];
        err.forEach(line => {
            const elErrorLine = document.createElement("p");
            elErrorLine.innerText = line;
            elErrorLine.classList.add('error-line');
            elError.appendChild(elErrorLine);
        });
        elErrorsList.appendChild(elError);
    });
}

function displayErrorTrace(trace, state) {
    const elErrorTrace = document.getElementById('error-trace');
    const elErrorTraceItems = document.getElementById('error-trace-items');
    removeAllChildren(elErrorTraceItems);
    if (!trace || trace.length === 0) {
        elErrorTrace.classList.add('hidden');
        return;
    }
    elErrorTrace.classList.remove('hidden');
    trace.forEach(item => displayErrorTraceItem(elErrorTraceItems, item, state));
    const expNodes = document.getElementsByClassName('tree-expandable');
    for (let i = 0; i < expNodes.length; i++) {
        expNodes[i].onclick = (e) => {
            const elName = e.target;
            elName.parentElement.parentElement.querySelector('.tree-nodes').classList.toggle('shown');
            elName.classList.toggle('tree-expandable-down');
        };
    }
}

function displayErrorTraceItem(elErrorTraceVars, item, state) {
    const elItem = document.createElement('li');
    const elItemBlock = document.createElement('div');
    elItemBlock.classList.add('error-trace-item-block');
    const elHeader = document.createElement('div');
    elHeader.classList.add('tree-node');
    elHeader.classList.add('tree-expandable');
    elHeader.classList.add('tree-expandable-down');
    elHeader.classList.add('error-trace-item-title');
    elHeader.innerText = `${item.num}: ${item.title}`;
    elItemBlock.appendChild(elHeader);
    elItem.appendChild(elItemBlock);
    const elVarList = document.createElement('ul');
    elVarList.classList.add('tree-nodes');
    elVarList.classList.add('hidden');
    elVarList.classList.add('shown');
    item.variables.items.forEach(v => displayValue(elVarList, v, state));
    elItem.appendChild(elVarList);
    elErrorTraceVars.appendChild(elItem);
}

function displayValue(elParent, value, state) {
    const elVar = document.createElement('li');
    const elVarValueBlock = document.createElement('div');
    const elVarKey = renderValueTitle(value, elVarValueBlock);
    elVarValueBlock.appendChild(elVarKey);
    const elVarValue = document.createElement('div');
    elVarValue.classList.add('var-value');
    elVarValue.innerText = value.str;
    if (value.changeType === 'D') {
        elVarValue.classList.add('value-deleted');
    }
    elVarValueBlock.appendChild(elVarValue);
    elVar.appendChild(elVarValueBlock);
    if (value.items && value.items.length > 0) {
        elVarKey.classList.add('tree-expandable');
        const elSubList = document.createElement('ul');
        elSubList.classList.add('tree-nodes');
        elSubList.classList.add('hidden');
        value.items.forEach(it => displayValue(elSubList, it, state));
        if (value.deletedItems) {
            value.deletedItems.forEach(dit => displayValue(elSubList, dit, state));
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
    elVarKey.textContent = value.key;
    if (value.changeType === 'D') {
        elVarKey.classList.add('value-deleted');
    }
    elVarTitle.appendChild(elVarKey);
    if (value.items) {
        const elVarSize = document.createElement('span');
        elVarSize.classList.add('var-size');
        elVarSize.textContent = `(${value.items.length})`;
        elVarSize.setAttribute('title', 'Size of the collection');
        elVarTitle.appendChild(elVarSize);
    }
    const elVarChange = document.createElement('span');
    if (value.changeType !== 'N') {
        elVarChange.classList.add('change-marker');
        elVarChange.classList.add('change-marker-' + value.changeType);
        elVarChange.textContent = value.changeType;
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
    lines.forEach(line => {
        const elLine = document.createElement('p');
        elLine.classList.add('output-line');
        let elText;
        if (line.count === 1) {
            elText = elLine;
        } else {
            elText = document.createElement('span');
            elLine.appendChild(elText);
            elCount = document.createElement('span');
            elCount.classList = ['output-line-count'];
            elCount.innerText = String(line.count);
            elCount.setAttribute('title', 'Number of consecutive occurrences');
            elLine.appendChild(elCount);
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
