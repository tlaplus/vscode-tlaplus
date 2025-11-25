import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { LANG_TLAPLUS } from '../common';
import { getNonce } from '../panels/utilities/getNonce';

export const CMD_OPEN_SPECTACLE = 'tlaSpectacle.open';

export async function openSpectacle(context: vscode.ExtensionContext): Promise<void> {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('Open a TLA+ specification to view it in Spectacle.');
        return;
    }
    if (editor.document.languageId !== LANG_TLAPLUS) {
        vscode.window.showWarningMessage('Spectacle can only open files with the TLA+ language mode.');
        return;
    }

    const document = editor.document;
    const panelTitle = `Spectacle - ${path.basename(document.fileName)}`;
    const spectacleRoot = vscode.Uri.joinPath(context.extensionUri, 'resources', 'spectacle');
    const panel = vscode.window.createWebviewPanel(
        'tlaSpectacle',
        panelTitle,
        { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
        {
            enableScripts: true,
            retainContextWhenHidden: true,
            localResourceRoots: [spectacleRoot],
        }
    );

    const glassesIcon = vscode.Uri.joinPath(spectacleRoot, 'assets', 'glasses-svgrepo-com.svg');
    panel.iconPath = { light: glassesIcon, dark: glassesIcon };

    panel.webview.html = buildSpectacleHtml(panel.webview, context.extensionUri);

    const initPayload = {
        type: 'spectacle:init',
        specText: document.getText(),
        specUri: document.uri.toString(true),
    };

    const messageDisposable = panel.webview.onDidReceiveMessage((message) => {
        if (message?.type === 'spectacle:webview-ready') {
            void panel.webview.postMessage(initPayload);
        }
    });

    panel.onDidDispose(() => messageDisposable.dispose());
}

export function buildSpectacleHtml(webview: vscode.Webview, extensionUri: vscode.Uri): string {
    const spectacleRoot = vscode.Uri.joinPath(extensionUri, 'resources', 'spectacle');
    const indexPath = vscode.Uri.joinPath(spectacleRoot, 'index.html').fsPath;
    const rawHtml = fs.readFileSync(indexPath, 'utf8');
    const baseUri = webview.asWebviewUri(spectacleRoot).toString();
    const nonce = getNonce();
    const csp = [
        "default-src 'none'",
        `img-src ${webview.cspSource} data:`,
        `style-src ${webview.cspSource} 'unsafe-inline'`,
        `font-src ${webview.cspSource}`,
        `worker-src ${webview.cspSource}`,
        `connect-src ${webview.cspSource}`,
        `script-src ${webview.cspSource} 'nonce-${nonce}' 'unsafe-eval' 'wasm-unsafe-eval'`,
    ].join('; ');

    const bootstrapScript = `    <script nonce="${nonce}">
        window.SPECTACLE_BASE_URL=${JSON.stringify(baseUri)};
        window.SPECTACLE_ENABLE_LOCAL_SERVER=false;
        window.SPECTACLE_ROUTER_DISABLE_HISTORY=true;
    </script>`;
    const baseInjection = `    <base href="${baseUri}/">
    <meta http-equiv="Content-Security-Policy" content="${csp}">
${bootstrapScript}`;

    let html = rawHtml.replace('<head>', `<head>
${baseInjection}`);
    html = html.replace(/<script(?![^>]*nonce=)/g, `<script nonce="${nonce}"`);
    return html;
}
