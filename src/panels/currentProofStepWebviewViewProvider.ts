import * as vscode from 'vscode';
import { TlapsProofStepDetails } from '../model/tlaps';
import { getNonce } from './utilities/getNonce';
import { getUri } from './utilities/getUri';
import { revealFile } from './utilities/workspace';
import { Location } from 'vscode-languageclient';
import { ProofStateIcons, proofStateIcons, proofStateNames } from '../tlaps';

export class CurrentProofStepWebviewViewProvider implements vscode.WebviewViewProvider {
    public static readonly viewType = 'tlaplus.current-proof-step';
    private view: vscode.WebviewView | null = null;
    private context: vscode.WebviewViewResolveContext | null = null;

    constructor(
        private readonly extensionUri: vscode.Uri
    ) { }

    public resolveWebviewView(
        view: vscode.WebviewView,
        context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        this.context = context;
        this.view = view;
        this.view.webview.options = { enableScripts: true };
        this.view.webview.html = this.makeHtml(this.view.webview);
        this.view.webview.onDidReceiveMessage(message => this.onMessage(message));
    }

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    private onMessage(message: any) {
        if (message.command === 'showLocation') {
            const location = message.location as Location;
            const uri = vscode.Uri.parse(location.uri);
            revealFile(
                uri.fsPath,
                vscode.ViewColumn.One,
                location.range.start.line,
                location.range.start.character
            );
        } else {
            console.log('unknown message from webview: ', message);
        }
    }

    public showProofStepDetails(tlapsProofStepDetails: TlapsProofStepDetails | null) {
        this.view?.webview.postMessage({
            command: 'tlapsProofStepDetails',
            details: tlapsProofStepDetails
        });
    }

    private makeHtml(webview: vscode.Webview) {
        const webviewUri = getUri(webview, this.extensionUri, ['out', 'current-proof-step.js']);
        const styleUri = getUri(webview, this.extensionUri, ['out', 'current-proof-step.css']);
        const nonce = getNonce();

        const webviewProofStateNames = Object.values(proofStateNames);
        const webviewProofStateIcons: ProofStateIcons = {};
        Object.values(proofStateNames).forEach(stateName => {
            const localPath = proofStateIcons[stateName];
            const onDiskPath = vscode.Uri.joinPath(this.extensionUri, localPath);
            const onViewPath = webview.asWebviewUri(onDiskPath);
            webviewProofStateIcons[stateName] = onViewPath.toString();
        });

        // Tip: Install the es6-string-html VS Code extension to enable code highlighting below
        /* eslint-disable max-len */
        return /*html*/ `
        <!DOCTYPE html>
        <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <meta http-equiv="Content-Security-Policy" content="default-src ${webview.cspSource}; style-src ${webview.cspSource}; font-src ${webview.cspSource}; script-src 'nonce-${nonce}';">
                <link rel="stylesheet" href="${styleUri}">
                <title>Current proof step</title>
                <script nonce="${nonce}">
                    const webviewProofStateNames = ${JSON.stringify(webviewProofStateNames)};
                    const webviewProofStateIcons = ${JSON.stringify(webviewProofStateIcons)};
                </script>
            </head>
            <body>
                <div id="root"></div>
                <script type="module" nonce="${nonce}" src="${webviewUri}"></script>
            </body>
        </html>
        `;
    }
}
