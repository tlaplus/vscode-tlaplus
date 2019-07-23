const vscode = acquireVsCodeApi();

const elTimeStart = document.getElementById('time-start');
const elTimeEnd = document.getElementById('time-end');
const elStatus = document.getElementById('check-status');
const elStatesStat = document.getElementById('states-stat');
const elCoverageStat = document.getElementById('coverage-stat');

const prevState = vscode.getState();
if (prevState) {
    updateCheckResult(prevState.checkResult);
}

function updateCheckResult(res) {
    if (!res) {
        return;
    }
    elTimeStart.textContent = res.startDateTimeStr;
    elTimeEnd.textContent = res.endDateTimeStr;
    elStatus.textContent = res.statusName + ' : ' + res.state;
    elStatus.classList = ['state-' + res.state];
    elStatesStat.innerHTML = res.initialStatesStat
        .map(s => `<tr><td>${s.timeStamp}</td><td class="number-col">${num(s.diameter)}</td><td class="number-col">${num(s.total)}</td><td class="number-col">${num(s.distinct)}</td><td class="number-col">${num(s.queueSize)}</td></tr>`)
        .join('');
    elCoverageStat.innerHTML = res.coverageStat
        .map(s => `<tr><td>${s.module}</td><td>${s.action}</td><td class="number-col">${num(s.total)}</td><td class="number-col">${num(s.distinct)}</td></tr>`)
        .join('');
    displayErrors(res.errors);
    displayErrorTrace(res.errorTrace);
}

window.addEventListener('message', event => {
    updateCheckResult(event.data.checkResult);
    vscode.setState(event.data);
});

function displayErrors(errors) {
    const elErrors = document.getElementById('errors');
    if (!errors || errors.length === 0) {
        elErrors.classList = ['hidden'];
        return;
    }
    elErrors.classList = [];
    const elErrorsList = document.getElementById('errors-list');
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

function displayErrorTrace(trace) {
    const elErrorTrace = document.getElementById('error-trace');
    if (!trace || trace.length === 0) {
        elErrorTrace.classList = ['hidden'];
        return;
    }
    elErrorTrace.classList = [];
    const elErrorTraceVars = document.getElementById('error-trace-variables');
    const errTraceRows = [];
    trace.forEach(item => {
        errTraceRows.push(`<tr><td colspan='2'><b>${item.num}: ${item.title}</b></td></tr>`);
        item.variables.forEach(v => {
            errTraceRows.push(`<tr><td>${v.name}</td><td>${v.value.str}</td></tr>`);
        });
    });
    elErrorTraceVars.innerHTML = errTraceRows.join('');
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
        parts.push(r);
        en = (en - r) / 1000;
    }
    return sign + parts.reverse().join(' ');
}
