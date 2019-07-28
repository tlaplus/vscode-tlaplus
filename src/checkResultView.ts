import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { ModelCheckResult } from './model/check';

// Cached HTML template for the WebView
let viewHtml: string | undefined;
let viewPanel: vscode.WebviewPanel | undefined;
let missingCheckResult: ModelCheckResult | null;
let panelIsVisible = false;

export function updateCheckResultView(checkResult: ModelCheckResult) {
    if (viewPanel && viewPanel.visible) {
        viewPanel.webview.postMessage({
            checkResult: checkResult
        });
        missingCheckResult = null;
    } else {
        missingCheckResult = checkResult;
    }
}

export function revealCheckResultView(checkResult: ModelCheckResult, extContext: vscode.ExtensionContext) {
    if (!viewPanel) {
        createNewPanel();
        ensurePanelBody(extContext);
    } else {
        viewPanel.reveal();
    }
    updateCheckResultView(checkResult);
}

function createNewPanel() {
    const title = 'TLA+ model checking';
    viewPanel = vscode.window.createWebviewPanel(
        'modelChecking',
        title,
        vscode.ViewColumn.Beside,
        {
            enableScripts: true,
            localResourceRoots: [vscode.Uri.file(path.resolve(__dirname, '../assets'))]
        }
    );
    viewPanel.onDidDispose(() => {
        viewPanel = undefined;
    });
    viewPanel.onDidChangeViewState(e => {
        if (e.webviewPanel.visible && !panelIsVisible && missingCheckResult) {
            // Show what has been missed while the panel was invisible
            updateCheckResultView(missingCheckResult);
        }
        panelIsVisible = e.webviewPanel.visible;
    });
    panelIsVisible = true;
}

function ensurePanelBody(extContext: vscode.ExtensionContext) {
    if (!viewPanel) {
        return;
    }
    const assetsDiskPath = vscode.Uri.file(
        path.join(extContext.extensionPath, 'assets')
    );
    const assetsPath = assetsDiskPath.with({ scheme: 'vscode-resource' });
    if (!viewHtml) {
        viewHtml = fs.readFileSync(path.join(assetsPath.fsPath, 'check-result-view.html'), 'utf8');
    }
    viewHtml = viewHtml.replace(/\${assetsPath}/g, String(assetsPath));
    viewPanel.webview.html = viewHtml;
}
