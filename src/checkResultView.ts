import * as vscode from 'vscode';
import { ModelCheckResult } from './parsers/modelChecker';

let viewPanel: vscode.WebviewPanel | null = null;

export function updateCheckResultView(checkResult: ModelCheckResult | null) {
    if (viewPanel) {
        viewPanel.webview.html = createModelCheckResultView(checkResult);
    }
}

export function revealCheckResultView(checkResult: ModelCheckResult | null) {
    const title = `TLA+ model checking`;
    if (viewPanel !== null) {
        viewPanel.title = title;
        viewPanel.reveal();
    } else {
        viewPanel = vscode.window.createWebviewPanel(
            'modelChecking',
            title,
            vscode.ViewColumn.One,
            {}
        );    
        viewPanel.onDidDispose(() => {
            viewPanel = null;
        });
    }
    viewPanel.webview.html = createModelCheckResultView(checkResult);
}

function createModelCheckResultView(checkResult: ModelCheckResult | null): string {
    const html: string[] = [];
    html.push(`<!DOCTYPE html><html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Model checking</title>
</head>
<body>`);
    if (checkResult !== null) {
        html.push(`Process: ${checkResult.getProcessInfo()}<br/>`);
        html.push(`Status: ${checkResult.getStatus()}<br/>`);
    }
    html.push(`</body></html>`);
    return html.join('');
}

