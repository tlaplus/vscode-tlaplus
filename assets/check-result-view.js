const vscode = acquireVsCodeApi();

const elTimes = document.getElementById('times');
const elStatus = document.getElementById('check-status');
const elStatesStat = document.getElementById('states-stat');
const elCoverageStat = document.getElementById('coverage-stat');
const elErrors = document.getElementById('errors');
const elErrorTrace = document.getElementById('error-trace');

const prevState = vscode.getState();
if (prevState) {
    updateCheckResult(prevState.checkResult);
}

function updateCheckResult(res) {
    elTimes.textContent = (res.startDateTime || '-') + ' - ' + (res.endDateTime || '-') + ', finished in ' + (res.duration || '?') + ' ms';
    elStatus.textContent = res.statusName + ' : ' + res.state;
    elStatus.classList = ['state-' + res.state];
    elStatesStat.innerHTML = res.initialStatesStat
        .map(s => `<tr><td>${s.time}</td><td>${s.diameter}</td><td>${s.total}</td><td>${s.distinct}</td><td>${s.queueSize}</td></tr>`)
        .join('');
    elCoverageStat.innerHTML = res.coverageStat
        .map(s => `<tr><td>${s.module}</td><td>${s.action}</td><td>${s.location}</td><td>${s.total}</td><td>${s.distinct}</td></tr>`)
        .join('');
    elErrors.innerText = res.errors
        .map(e => e.join('\n'))
        .join('');
    const errTraceRows = [];
    res.errorTrace.forEach(item => {
        errTraceRows.push(`<tr><td colspan='2'><b>${item.num}: ${item.title}</b></td></tr>`);
        item.variables.forEach(v => {
            errTraceRows.push(`<tr><td>${v.name}</td><td>${v.value.str}</td></tr>`);
        });
    });
    elErrorTrace.innerHTML = errTraceRows.join('');
}

window.addEventListener('message', event => {
    updateCheckResult(event.data.checkResult);
    vscode.setState(event.data);
});
