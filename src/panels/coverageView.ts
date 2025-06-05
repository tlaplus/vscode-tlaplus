import * as vscode from 'vscode';
import * as fs from 'fs';
import { getNonce } from './utilities/getNonce';
import { getUri } from './utilities/getUri';
import { CoverageData } from '../model/coverage';
import { parseNDJSON } from '../parsers/ndjson';

export class CoverageViewPanel {
    private static readonly viewType = 'coverageVisualization';
    private static currentPanel: CoverageViewPanel | undefined;

    private readonly panel: vscode.WebviewPanel;
    private readonly extensionUri: vscode.Uri;
    private readonly disposables: vscode.Disposable[] = [];
    private fileUri: vscode.Uri;
    private fileWatcher: vscode.FileSystemWatcher | undefined;

    private constructor(extensionUri: vscode.Uri, fileUri: vscode.Uri) {
        this.extensionUri = extensionUri;
        this.fileUri = fileUri;

        this.panel = vscode.window.createWebviewPanel(
            CoverageViewPanel.viewType,
            `Coverage: ${vscode.workspace.asRelativePath(fileUri)}`,
            vscode.ViewColumn.Beside,
            {
                enableScripts: true,
                retainContextWhenHidden: true,
                localResourceRoots: [vscode.Uri.joinPath(extensionUri, 'out')]
            }
        );

        this.panel.iconPath = {
            light: vscode.Uri.joinPath(extensionUri, 'resources', 'images', 'tlaplus-nightly.png'),
            dark: vscode.Uri.joinPath(extensionUri, 'resources', 'images', 'tlaplus-nightly.png')
        };

        this.panel.webview.html = this.getWebviewContent(this.panel.webview);

        this.panel.webview.onDidReceiveMessage(
            message => this.handleMessage(message),
            undefined,
            this.disposables
        );

        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);

        // Set up file watcher
        this.setupFileWatcher();

        // Load initial data
        this.loadAndSendData();
    }

    public static render(extensionUri: vscode.Uri, fileUri: vscode.Uri): void {
        if (CoverageViewPanel.currentPanel) {
            CoverageViewPanel.currentPanel.fileUri = fileUri;
            CoverageViewPanel.currentPanel.panel.title = `Coverage: ${vscode.workspace.asRelativePath(fileUri)}`;
            CoverageViewPanel.currentPanel.setupFileWatcher();
            CoverageViewPanel.currentPanel.loadAndSendData();
            CoverageViewPanel.currentPanel.panel.reveal(vscode.ViewColumn.Beside);
        } else {
            CoverageViewPanel.currentPanel = new CoverageViewPanel(extensionUri, fileUri);
        }
    }

    private setupFileWatcher(): void {
        // Dispose existing watcher
        if (this.fileWatcher) {
            this.fileWatcher.dispose();
        }

        // Create new watcher
        this.fileWatcher = vscode.workspace.createFileSystemWatcher(this.fileUri.fsPath);

        this.fileWatcher.onDidChange(() => {
            this.loadAndSendData();
        }, undefined, this.disposables);

        this.fileWatcher.onDidDelete(() => {
            vscode.window.showWarningMessage('Coverage file was deleted');
            this.panel.webview.postMessage({ type: 'fileDeleted' });
        }, undefined, this.disposables);
    }

    private async loadAndSendData(): Promise<void> {
        try {
            const content = await fs.promises.readFile(this.fileUri.fsPath, 'utf-8');
            const stats = parseNDJSON(content);

            const coverageData: CoverageData = {
                stats,
                fileName: vscode.workspace.asRelativePath(this.fileUri),
                lastUpdated: new Date()
            };

            this.panel.webview.postMessage({
                type: 'update',
                data: coverageData
            });
        } catch (error) {
            vscode.window.showErrorMessage(`Failed to read coverage file: ${error}`);
        }
    }

    private handleMessage(message: { type: string }): void {
        switch (message.type) {
            case 'ready':
                this.loadAndSendData();
                break;
            case 'refresh':
                this.loadAndSendData();
                break;
        }
    }

    private getWebviewContent(webview: vscode.Webview): string {
        const nonce = getNonce();
        const scriptUri = getUri(webview, this.extensionUri, ['out', 'coverageView.js']);
        const styleUri = getUri(webview, this.extensionUri, ['out', 'coverageView.css']);
        const codiconsUri = getUri(webview, this.extensionUri, ['out', 'codicon.css']);

        return `<!DOCTYPE html>
            <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <meta http-equiv="Content-Security-Policy"
                    content="default-src 'none'; style-src ${webview.cspSource} 'unsafe-inline'; script-src 'nonce-${nonce}'; font-src ${webview.cspSource};">
                <link href="${styleUri}" rel="stylesheet">
                <link href="${codiconsUri}" rel="stylesheet">
                <title>Coverage Visualization</title>
            </head>
            <body>
                <div id="root"></div>
                <script nonce="${nonce}" src="${scriptUri}"></script>
            </body>
            </html>`;
    }

    private dispose(): void {
        CoverageViewPanel.currentPanel = undefined;

        if (this.fileWatcher) {
            this.fileWatcher.dispose();
        }

        this.panel.dispose();

        while (this.disposables.length) {
            const disposable = this.disposables.pop();
            if (disposable) {
                disposable.dispose();
            }
        }
    }
}