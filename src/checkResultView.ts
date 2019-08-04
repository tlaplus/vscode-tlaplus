import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { ModelCheckResult } from './model/check';
import { CMD_CHECK_MODEL_STOP } from './commands/checkModel';

// Cached HTML template for the WebView
let viewHtml: string | undefined;
let viewPanel: vscode.WebviewPanel | undefined;
let missing: boolean;
let lastCheckResult: ModelCheckResult | undefined;
let panelIsVisible = false;

export function updateCheckResultView(checkResult: ModelCheckResult) {
    if (viewPanel && viewPanel.visible) {
        viewPanel.webview.postMessage({
            checkResult: checkResult
        });
        missing = false;
    } else {
        missing = true;
    }
    lastCheckResult = checkResult;
}

export function revealEmptyCheckResultView(extContext: vscode.ExtensionContext) {
    doRevealCheckResultView(extContext);
    updateCheckResultView(ModelCheckResult.EMPTY);
}

export function revealCheckResultView(extContext: vscode.ExtensionContext) {
    doRevealCheckResultView(extContext);
    updateCheckResultView(lastCheckResult ? lastCheckResult : ModelCheckResult.EMPTY);
}

function doRevealCheckResultView(extContext: vscode.ExtensionContext) {
    if (!viewPanel) {
        createNewPanel();
        ensurePanelBody(extContext);
    } else {
        viewPanel.reveal();
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
            localResourceRoots: [vscode.Uri.file(path.resolve(__dirname, '../resources'))]
        }
    );
    viewPanel.iconPath = vscode.Uri.file(path.resolve(__dirname, '../resources/images/result-ico.svg'));
    viewPanel.onDidDispose(() => {
        viewPanel = undefined;
    });
    viewPanel.onDidChangeViewState(e => {
        if (e.webviewPanel.visible && !panelIsVisible && missing && lastCheckResult) {
            // Show what has been missed while the panel was invisible
            updateCheckResultView(lastCheckResult);
        }
        panelIsVisible = e.webviewPanel.visible;
    });
    viewPanel.webview.onDidReceiveMessage(message => {
        if (message.command === 'stop') {
            vscode.commands.executeCommand(CMD_CHECK_MODEL_STOP);
        }
    });
    panelIsVisible = true;
}

function ensurePanelBody(extContext: vscode.ExtensionContext) {
    if (!viewPanel) {
        return;
    }
    const resourcesDiskPath = vscode.Uri.file(
        path.join(extContext.extensionPath, 'resources')
    );
    const resourcesPath = resourcesDiskPath.with({ scheme: 'vscode-resource' });
    if (!viewHtml) {
        viewHtml = fs.readFileSync(path.join(resourcesPath.fsPath, 'check-result-view.html'), 'utf8');
    }
    viewHtml = viewHtml.replace(/\${resourcesPath}/g, String(resourcesPath));
    viewPanel.webview.html = viewHtml;
}
