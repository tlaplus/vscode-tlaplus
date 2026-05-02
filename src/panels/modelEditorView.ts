import * as path from 'path';
import * as vscode from 'vscode';
import { getNonce } from './utilities/getNonce';
import { getUri } from './utilities/getUri';

export const CMD_MODEL_EDITOR_DISPLAY = 'tlaplus.model.editor.display';
const PANEL_VIEW_TYPE = 'tlaplus.modelEditor';
const PANEL_TITLE = 'TLA+ Model Editor';

/**
 * Entry point for the "Open with Model Editor" command.
 */
export function showModelEditor(
    context: vscode.ExtensionContext,
    uri?: vscode.Uri
): void {
    const fileUri = uri ?? vscode.window.activeTextEditor?.document.uri;
    if (!fileUri) {
        void vscode.window.showWarningMessage(
            'No TLA+ specification file is open.'
        );
        return;
    }

    const panel = vscode.window.createWebviewPanel(
        PANEL_VIEW_TYPE,
        `${PANEL_TITLE}: ${path.basename(fileUri.fsPath)}`,
        vscode.ViewColumn.Beside,
        { enableScripts: true }
    );
    configureWebview(panel, context.extensionUri);
}

function configureWebview(
    panel: vscode.WebviewPanel,
    extensionUri: vscode.Uri
): void {
    panel.webview.options = {
        enableScripts: true,
        localResourceRoots: [vscode.Uri.joinPath(extensionUri, 'out')]
    };
    panel.webview.html = getWebviewHtml(panel.webview, extensionUri);
}

function getWebviewHtml(
    webview: vscode.Webview,
    extensionUri: vscode.Uri
): string {
    const scriptUri = getUri(webview, extensionUri, ['out', 'model-editor.js']);
    const nonce = getNonce();
    /* eslint-disable max-len */
    return /*html*/ `
        <!DOCTYPE html>
        <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline' ${webview.cspSource}; script-src 'nonce-${nonce}';">
                <title>${PANEL_TITLE}</title>
            </head>
            <body>
                <div id="root"></div>
                <script type="module" nonce="${nonce}" src="${scriptUri}"></script>
            </body>
        </html>
    `;
    /* eslint-enable max-len */
}
