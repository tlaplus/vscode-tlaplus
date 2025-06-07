import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { CoverageData } from '../model/coverage';
import { CoverageChart } from './coverageView/coverageChart';
import { CoverageHeader } from './coverageView/coverageHeader';
import { CoverageFileDeleted } from './coverageView/coverageFileDeleted';
import { vscode } from './coverageView/vscode';

import '@vscode/codicons/dist/codicon.css';
import './coverageView/index.css';

type ViewState =
    | { type: 'loading' }
    | { type: 'loaded'; data: CoverageData }
    | { type: 'file-deleted'; fileName?: string }
    | { type: 'error'; message: string };

interface CoverageViewAppProps {
    state: ViewState;
}

const CoverageViewApp = React.memo(({ state }: CoverageViewAppProps) => {
    return (
        <React.StrictMode>
            <div className="coverage-view-container">
                {(() => {
                    switch (state.type) {
                        case 'loading':
                            return (
                                <div className="loading">
                                    <p>Loading coverage data...</p>
                                </div>
                            );
                        case 'loaded':
                            return (
                                <>
                                    <CoverageHeader data={state.data} />
                                    <CoverageChart data={state.data} />
                                </>
                            );
                        case 'file-deleted':
                            return <CoverageFileDeleted fileName={state.fileName} />;
                        case 'error':
                            return (
                                <div className="error">
                                    <p>Error: {state.message}</p>
                                </div>
                            );
                    }
                })()}
            </div>
        </React.StrictMode>
    );
});

const root = createRoot(document.getElementById('root') as HTMLElement);

let lastKnownFileName: string | undefined;

function render(state: ViewState) {
    root.render(<CoverageViewApp state={state} />);
}

// Handle messages from extension
window.addEventListener('message', (event) => {
    const message = event.data;

    switch (message.type) {
        case 'update':
            vscode.setState(message.data);
            if (message.data) {
                lastKnownFileName = message.data.fileName;
                render({ type: 'loaded', data: message.data });
            }
            break;
        case 'fileDeleted':
            vscode.setState(null);
            render({ type: 'file-deleted', fileName: lastKnownFileName });
            break;
    }
});

// Load initial state
window.addEventListener('load', () => {
    const savedData = vscode.getState() as CoverageData | null;
    if (savedData) {
        lastKnownFileName = savedData.fileName;
        render({ type: 'loaded', data: savedData });
    } else {
        render({ type: 'loading' });
        // Signal to extension that webview is ready
        vscode.postMessage({ type: 'ready' });
    }
});