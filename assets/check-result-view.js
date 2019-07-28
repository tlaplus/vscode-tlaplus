const vscode = acquireVsCodeApi();

const prevState = vscode.getState();
if (prevState) {
    displayCheckResult(prevState);
}

function displayCheckResult(data) {
    const res = data.checkResult;
    displayStatus(res);
    displayStatesStat(res ? res.initialStatesStat : []);
    displayCoverage(res ? res.coverageStat: []);
    displayErrors(res ? res.errors : []);
    displayErrorTrace(res ? res.errorTrace : [], data);
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
    const elStatus = document.getElementById('check-status');
    elTimeStart.textContent = result ? result.startDateTimeStr : '-';
    elTimeEnd.textContent = result ? result.endDateTimeStr : '-';
    elStatus.textContent = result ? result.statusName + ' : ' + result.state : '-';
    elStatus.classList = result ? ['state-' + result.state] : [];
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
        elErrors.classList = ['hidden'];
        return;
    }
    elErrors.classList = [];
    errors.forEach(err => {
        const elError = document.createElement('p');
        elError.classList = ['error'];
        err.forEach(line => {
            const elErrorLine = document.createElement("p");
            elErrorLine.innerText = line;
            elErrorLine.classList = ['error-line'];
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
        elErrorTrace.classList = ['hidden'];
        return;
    }
    elErrorTrace.classList = [];
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
    const elHeader = document.createElement('span');
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
    item.variables
        .sort(compareVariables)
        .forEach(v => displayVariable(elVarList, v.name, v.value, state));
    elItem.appendChild(elVarList);
    elErrorTraceVars.appendChild(elItem);
}

function displayVariable(elParent, name, value, state) {
    let nameHtml = name;
    if (value.items) {
        nameHtml += ' <span class="var-size">(' + value.items.length + ')</span>';
    }
    const elVar = document.createElement('li');
    const elVarValueBlock = document.createElement('div');
    const elVarName = document.createElement('div');
    elVarName.classList.add('var-name');
    elVarName.classList.add('tree-node');
    elVarName.innerHTML = nameHtml;
    elVarValueBlock.appendChild(elVarName);
    const elVarValue = document.createElement('div');
    elVarValue.classList.add('var-value');
    elVarValue.innerText = value.str;
    elVarValueBlock.appendChild(elVarValue);
    elVar.appendChild(elVarValueBlock);
    if (value.items && value.items.length > 0) {
        elVarName.classList.add('tree-expandable');
        const elSubList = document.createElement('ul');
        elSubList.classList.add('tree-nodes');
        elSubList.classList.add('hidden');
        let idx = 1;
        value.items.forEach(it => {
            if (it.key) {
                displayVariable(elSubList, it.key, it.value, state);
            } else {
                displayVariable(elSubList, String(idx), it, state);
            }
            idx += 1;
        });
        elVar.appendChild(elSubList);
    }
    elParent.appendChild(elVar);
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

function compareVariables(a, b) {
    if (a.name < b.name) {
        return -1;
    } else if (a.name > b.name) {
        return 1;
    }
    return 0;
}
