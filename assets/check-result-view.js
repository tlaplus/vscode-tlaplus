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
    const elErrorTraceVars = document.getElementById('error-trace-variables');
    removeAllChildren(elErrorTraceVars);
    if (!trace || trace.length === 0) {
        elErrorTrace.classList = ['hidden'];
        return;
    }
    elErrorTrace.classList = [];
    trace.forEach(item => {
        const elHeaderRow = document.createElement('tr');
        const elHeaderCell = document.createElement('td');
        elHeaderCell.classList.add('error-trace-item-title');
        elHeaderCell.setAttribute('colspan', '2');
        elHeaderCell.innerText = `${item.num}: ${item.title}`;
        elHeaderRow.appendChild(elHeaderCell);
        elErrorTraceVars.appendChild(elHeaderRow);
        item.variables.forEach(v => {
            let nameHtml = v.name;
            if (v.value.items) {
                nameHtml += ' <span class="var-size">(' + v.value.items.length + ')</span>';
            }
            const elVarRow = document.createElement('tr');
            const elVarNameCell = document.createElement('td');
            elVarNameCell.classList.add('var-name');
            const elVarNamePrefix = document.createElement('div');
            elVarNamePrefix.classList.add('var-name-prefix');
            if (v.value.items && v.value.items.length > 0) {
                if (v.expanded === true) {
                    elVarNamePrefix.classList.add('var-collection-expanded');
                    elVarNamePrefix.innerText = '-';
                } else {
                    elVarNamePrefix.classList.add('var-collection-collapsed');
                    elVarNamePrefix.innerText = '+';
                }
                elVarNamePrefix.onclick = e => {
                    if (v.expanded === true) {
                        v.expanded = false;
                        e.srcElement.classList.remove('var-collection-expanded');
                        e.srcElement.classList.add('var-collection-collapsed');
                        e.srcElement.innerText = '+';
                    } else {
                        v.expanded = true;
                        e.srcElement.classList.remove('var-collection-collapsed');
                        e.srcElement.classList.add('var-collection-expanded');
                        e.srcElement.innerText = '-';
                    }
                    vscode.setState(state);
                };
            }
            elVarNameCell.appendChild(elVarNamePrefix);
            const elVarNameText = document.createElement('span');
            elVarNameText.innerHTML = nameHtml;
            elVarNameCell.appendChild(elVarNameText);
            elVarRow.appendChild(elVarNameCell);
            const elVarValueCell = document.createElement('td');
            elVarValueCell.classList.add('var-value');
            elVarValueCell.innerText = v.value.str;
            elVarRow.appendChild(elVarValueCell);
            elErrorTraceVars.appendChild(elVarRow);
        });
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
