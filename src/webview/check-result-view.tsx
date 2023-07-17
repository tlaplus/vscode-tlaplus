import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { ModelCheckResult } from '../model/check';
import { ErrorTraceSection } from './checkResultView/errorTraceSection';
import { HeaderSection } from './checkResultView/headerSection';
import { OutputSection } from './checkResultView/outputSection';
import { StatsSection } from './checkResultView/statsSection';
import { vscode } from './checkResultView/vscode';

import '@vscode/codicons/dist/codicon.css';

interface CheckResultViewAppI {state: ModelCheckResult}
const CheckResultViewApp = React.memo(({state}: CheckResultViewAppI) =>
    <React.StrictMode>
        {state && <HeaderSection checkResult={state}/>}
        {state && <StatsSection checkResult={state}/>}
        {state && <OutputSection checkResult={state}/>}
        {state && <ErrorTraceSection checkResult={state}/>}
    </React.StrictMode>
);

let root = createRoot(document.getElementById('root') as HTMLElement);

function render(checkResult: ModelCheckResult) {
    root.render(<CheckResultViewApp state={checkResult}/>);
}

window.addEventListener('message',
    (event) => {
        if (JSON.stringify(vscode.getState()) === JSON.stringify(event.data.checkResult)) {
            return;
        }

        // If it is data from a new run cleanup window to avoid visual bugs
        const prevState = vscode.getState() as ModelCheckResult;
        if (prevState
            && event.data.checkResult
            && prevState.startDateTimeStr !== event.data.checkResult.startDateTimeStr) {
            root.unmount();
            root = createRoot(document.getElementById('root') as HTMLElement);
        }

        vscode.setState(event.data.checkResult);
        render(event.data.checkResult);
    });

window.addEventListener('load', () => render(vscode.getState() as ModelCheckResult));
