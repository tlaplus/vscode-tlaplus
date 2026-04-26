import * as path from 'path';
import * as vscode from 'vscode';
import { getNonce } from './utilities/getNonce';
import { getUri } from './utilities/getUri';

export const CMD_MODEL_EDITOR_DISPLAY = 'tlaplus.model.editor.display';
export const MODEL_EDITOR_VIEW_TYPE = 'tlaplus.cfgEditor';
const CFG_MODEL_EDITOR_ENABLED = 'tlaplus.modelEditor.enabled';
const PANEL_VIEW_TYPE = 'tlaplus.modelEditor';
const PANEL_TITLE = 'TLA+ Model Editor';

function isModelEditorEnabled(): boolean {
    return vscode.workspace.getConfiguration()
        .get<boolean>(CFG_MODEL_EDITOR_ENABLED, false);
}

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

    if (fileUri.fsPath.endsWith('.cfg')) {
        void vscode.commands.executeCommand(
            'vscode.openWith', fileUri, MODEL_EDITOR_VIEW_TYPE,
            vscode.ViewColumn.Beside
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

/**
 * CustomTextEditorProvider for .cfg files, enabling
 * "Reopen Editor With..." → TLA+ Model Editor.
 *
 * Only registered while the feature flag is enabled.
 */
export class ModelEditorCfgProvider implements vscode.CustomTextEditorProvider {

    constructor(private readonly context: vscode.ExtensionContext) { }

    public resolveCustomTextEditor(
        _document: vscode.TextDocument,
        webviewPanel: vscode.WebviewPanel
    ): void {
        configureWebview(webviewPanel, this.context.extensionUri);
    }
}

/**
 * Registers the custom editor provider for the Model Editor and keeps
 * its registration in sync with the `tlaplus.modelEditor.enabled`
 * setting.
 */
export function registerModelEditor(
    context: vscode.ExtensionContext
): vscode.Disposable {
    let registration: vscode.Disposable | undefined;

    const sync = () => {
        const enabled = isModelEditorEnabled();
        if (enabled && !registration) {
            registration = vscode.window.registerCustomEditorProvider(
                MODEL_EDITOR_VIEW_TYPE,
                new ModelEditorCfgProvider(context),
                { supportsMultipleEditorsPerDocument: false }
            );
        } else if (!enabled && registration) {
            registration.dispose();
            registration = undefined;
        }
    };

    sync();

    const configListener = vscode.workspace.onDidChangeConfiguration((e) => {
        if (e.affectsConfiguration(CFG_MODEL_EDITOR_ENABLED)) {
            sync();
        }
    });

    return {
        dispose: () => {
            configListener.dispose();
            registration?.dispose();
            registration = undefined;
        }
    };
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
