import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { ModelCheckResult } from './parsers/modelChecker';

// Cached HTML template for the WebView
let viewHtml: string | undefined = undefined;
let viewPanel: vscode.WebviewPanel | null = null;
let lastCheckResult: ModelCheckResult | null;

export function updateCheckResultView(checkResult: ModelCheckResult | null) {
    setCheckResultView(checkResult);
    lastCheckResult = checkResult;
}

export function revealCheckResultView(checkResult: ModelCheckResult | null) {
    if (viewPanel === null) {
        createNewPanel();
        ensurePanelBody();
    } else {
        viewPanel.reveal();
    }
    updateCheckResultView(checkResult);
}

function setCheckResultView(checkResult: ModelCheckResult | null) {
    if (viewPanel) {
        viewPanel.webview.postMessage({
            checkResult: checkResult
        });
    }
}

function createNewPanel() {
    const title = `TLA+ model checking`;
    viewPanel = vscode.window.createWebviewPanel(
        'modelChecking',
        title,
        vscode.ViewColumn.One,
        {
            enableScripts: true,
            localResourceRoots: [vscode.Uri.file(path.resolve(__dirname, '../assets'))]
        }
    );
    viewPanel.onDidDispose(() => {
        viewPanel = null;
    });
    viewPanel.onDidChangeViewState(e => {
        if (e.webviewPanel.visible) {
            // Show what has been missed while the panel was invisible
            setCheckResultView(lastCheckResult);
        }
    });
}

function ensurePanelBody() {
    if (!viewPanel) {
        return;
    }
    if (!viewHtml) {
        viewHtml = fs.readFileSync(path.resolve(__dirname, '../assets/check-result-view.html'), 'utf8');
    }
    viewPanel.webview.html = viewHtml;
}