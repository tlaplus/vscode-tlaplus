import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { ModelCheckResult } from './model/check';

// Cached HTML template for the WebView
let viewHtml: string | undefined;
let viewPanel: vscode.WebviewPanel | undefined;
let lastCheckResult: ModelCheckResult | null;

export function updateCheckResultView(checkResult: ModelCheckResult | null) {
    setCheckResultView(checkResult);
    lastCheckResult = checkResult;
}

export function revealCheckResultView(checkResult: ModelCheckResult | null, extContext: vscode.ExtensionContext) {
    if (!viewPanel) {
        createNewPanel();
        ensurePanelBody(extContext);
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
        if (e.webviewPanel.visible) {
            // Show what has been missed while the panel was invisible
            setCheckResultView(lastCheckResult);
        }
    });
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
