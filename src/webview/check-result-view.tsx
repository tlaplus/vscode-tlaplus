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

const root = createRoot(document.getElementById('root') as HTMLElement);
const main = () => render(vscode.getState() as ModelCheckResult);

function render(checkResult: ModelCheckResult) {
    root.render(<CheckResultViewApp state={checkResult}/>);
}

window.addEventListener('message',
    (event) => {
        if (JSON.stringify(vscode.getState()) !== JSON.stringify(event.data.checkResult)) {
            vscode.setState(event.data.checkResult);
            render(event.data.checkResult);
        }
    });

window.addEventListener('load', main);
