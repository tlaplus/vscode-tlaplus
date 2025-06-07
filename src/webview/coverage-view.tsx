import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { CoverageData } from '../model/coverage';
import { CoverageChart } from './coverageView/coverageChart';
import { CoverageHeader } from './coverageView/coverageHeader';
import { vscode } from './coverageView/vscode';

import '@vscode/codicons/dist/codicon.css';

interface CoverageViewAppProps {
    data: CoverageData | null;
}

const CoverageViewApp = React.memo(({ data }: CoverageViewAppProps) => {
    return (
        <React.StrictMode>
            <div className="coverage-view-container">
                {data && <CoverageHeader data={data} />}
                {data && <CoverageChart data={data} />}
                {!data && (
                    <div className="loading">
                        <p>Loading coverage data...</p>
                    </div>
                )}
            </div>
        </React.StrictMode>
    );
});

const root = createRoot(document.getElementById('root') as HTMLElement);

function render(data: CoverageData | null) {
    root.render(<CoverageViewApp data={data} />);
}

// Handle messages from extension
window.addEventListener('message', (event) => {
    const message = event.data;

    switch (message.type) {
        case 'update':
            vscode.setState(message.data);
            render(message.data);
            break;
        case 'fileDeleted':
            render(null);
            break;
    }
});

// Load initial state
window.addEventListener('load', () => {
    const state = vscode.getState() as CoverageData | null;
    if (state) {
        render(state);
    } else {
        // Signal to extension that webview is ready
        vscode.postMessage({ type: 'ready' });
    }
});