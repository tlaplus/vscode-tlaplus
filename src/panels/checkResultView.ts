import * as vscode from 'vscode';
import { CMD_CHECK_MODEL_RUN_AGAIN, CMD_CHECK_MODEL_STOP, CMD_SHOW_TLC_OUTPUT } from '../commands/checkModel';
import { ModelCheckResult, ModelCheckResultSource } from '../model/check';
import { getNonce } from './utilities/getNonce';
import { getUri } from './utilities/getUri';
import { createDocument, revealFile } from './utilities/workspace';
import { TLAPLUS_DEBUG_LOAD_TRACE } from '../debugger/debugging';

export class CheckResultViewController implements vscode.Disposable {
    private currentPanel: CheckResultPanel | undefined;
    private lastCheckResult: ModelCheckResult | undefined;

    constructor(private readonly extensionUri: vscode.Uri) {}

    updateCheckResult(checkResult: ModelCheckResult): void {
        this.lastCheckResult = checkResult;
        this.currentPanel?.updateView(checkResult);
    }

    revealEmpty(): void {
        const preserveFocus = vscode.workspace.getConfiguration()
            .get<boolean>('tlaplus.tlc.modelChecker.preserveEditorFocus') ?? false;
        const previousEditor = preserveFocus ? vscode.window.activeTextEditor : undefined;
        const panel = this.ensurePanel();
        this.updateCheckResult(ModelCheckResult.createEmpty(ModelCheckResultSource.Process));
        panel.reveal(preserveFocus);
        if (preserveFocus && previousEditor) {
            void vscode.window.showTextDocument(previousEditor.document, previousEditor.viewColumn, true);
        }
    }

    revealLastResult(): void {
        const preserveFocus = vscode.workspace.getConfiguration()
            .get<boolean>('tlaplus.tlc.modelChecker.preserveEditorFocus') ?? false;
        const previousEditor = preserveFocus ? vscode.window.activeTextEditor : undefined;
        const panel = this.ensurePanel();
        this.updateCheckResult(this.lastCheckResult ?? ModelCheckResult.createEmpty(ModelCheckResultSource.Process));
        panel.reveal(preserveFocus);
        if (preserveFocus && previousEditor) {
            void vscode.window.showTextDocument(previousEditor.document, previousEditor.viewColumn, true);
        }
    }

    isFocused(): boolean {
        return this.currentPanel?.isFocused() ?? false;
    }

    dispose(): void {
        this.currentPanel?.dispose();
        this.currentPanel = undefined;
    }

    private ensurePanel(): CheckResultPanel {
        if (!this.currentPanel) {
            this.currentPanel = new CheckResultPanel(this.extensionUri, () => {
                this.currentPanel = undefined;
            });
        }
        return this.currentPanel;
    }
}

class CheckResultPanel implements vscode.Disposable {
    private static readonly viewType = 'modelChecking';

    private readonly panel: vscode.WebviewPanel;
    private readonly disposables: vscode.Disposable[] = [];
    private checkResult: ModelCheckResult;

    constructor(
        private readonly extensionUri: vscode.Uri,
        private readonly onDisposePanel: () => void,
    ) {
        this.checkResult = ModelCheckResult.createEmpty(ModelCheckResultSource.Process);
        const preserveFocus = vscode.workspace.getConfiguration()
            .get<boolean>('tlaplus.tlc.modelChecker.preserveEditorFocus');

        this.panel = vscode.window.createWebviewPanel(
            CheckResultPanel.viewType,
            'TLA+ model checking',
            { viewColumn: vscode.ViewColumn.Beside, preserveFocus },
            {
                enableScripts: true,
                retainContextWhenHidden: true,
                localResourceRoots: [vscode.Uri.joinPath(extensionUri, 'out')]
            }
        );

        this.panel.iconPath = {
            dark: vscode.Uri.joinPath(extensionUri, 'resources', 'images', 'preview-dark.svg'),
            light: vscode.Uri.joinPath(extensionUri, 'resources', 'images', 'preview-light.svg'),
        };
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);
        this.panel.webview.html = this.getWebviewContent();
        this.panel.webview.onDidReceiveMessage((message) => this.handleWebviewMessage(message));
    }

    updateView(checkResult: ModelCheckResult): void {
        this.checkResult = checkResult;
        void this.panel.webview.postMessage({ checkResult });
    }

    reveal(preserveFocus: boolean): void {
        this.panel.reveal(undefined, preserveFocus);
    }

    isFocused(): boolean {
        return this.panel.active;
    }

    dispose(): void {
        this.onDisposePanel();
        this.panel.dispose();
        while (this.disposables.length) {
            this.disposables.pop()?.dispose();
        }
    }

    private formatErrorTrace(): string {
        if (!this.checkResult || !this.checkResult.errors || this.checkResult.errors.length === 0) {
            return 'No counterexample available.';
        }

        const traces: string[] = [];
        for (const error of this.checkResult.errors) {
            if (!error.errorTrace || error.errorTrace.length === 0) {
                continue;
            }
            const stateLines: string[] = [];
            for (const traceItem of error.errorTrace) {
                stateLines.push(`${traceItem.num}: <${traceItem.title}>`);
                if (traceItem.variables && traceItem.variables.items) {
                    for (const variable of traceItem.variables.items) {
                        const formattedValue = variable.format('');
                        stateLines.push(`/\\ ${variable.key} = ${formattedValue}`);
                    }
                }
                stateLines.push('');
            }
            traces.push(stateLines.join('\n'));
        }
        return traces.join('\n---\n\n') || 'No counterexample available.';
    }

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    private handleWebviewMessage(message: any) {
        if (message.command === 'stop') {
            void vscode.commands.executeCommand(CMD_CHECK_MODEL_STOP);
        } else if (message.command === 'showTlcOutput') {
            void vscode.commands.executeCommand(CMD_SHOW_TLC_OUTPUT);
        } else if (message.command === 'runAgain') {
            void vscode.commands.executeCommand(CMD_CHECK_MODEL_RUN_AGAIN);
        } else if (message.command === 'debugCounterexample') {
            const specFiles = this.checkResult?.specFiles;
            if (specFiles && typeof specFiles === 'object' && 'tlaFilePath' in specFiles) {
                void vscode.commands.executeCommand(TLAPLUS_DEBUG_LOAD_TRACE, specFiles.tlaFilePath);
            } else {
                vscode.window.showWarningMessage('No specification file available for debugging');
            }
        } else if (message.command === 'openAIChat') {
            const traceText = this.formatErrorTrace();
            const prompt = `Help me analyze this TLA+ counterexample/trace.

**Counterexample:**
\`\`\`
${traceText}
\`\`\`

**Available TLA+ MCP Tools & Resources:**

1. **tlaplus_mcp_tlc_trace** - Load and replay the counterexample stored in the trace file with custom ALIAS expressions to:
   - Filter or rename variables for clarity
   - Compute derived values that help explain the behavior
   - Trace files are in .vscode/tlc/ with pattern: {specName}_trace_T{timestamp}_F{fp}_W{workers}_M{mode}.tlc

2. **Knowledge Resources:**
   - tlaplus://knowledge/tla-diagnose-property-violations.md - Strategies for debugging invariant and property violations
   - tlaplus://knowledge/tlc-alias-expressions.md - Comprehensive guide on using ALIAS expressions for trace analysis

3. **Other Useful Tools:**
   - tlaplus_mcp_tlc_check - Re-run model checking with modified configuration
   - tlaplus_mcp_tlc_explore - Generate example behaviors to understand expected traces
   - tlaplus_mcp_sany_symbol - Extract specification symbols to understand the model structure

**Please help me:**
1. Understand what went wrong in this counterexample
2. Identify which invariant or property was violated and why
3. Suggest ALIAS expressions to make the trace more readable
4. Recommend next steps for fixing the specification or finding the root cause`;
            void vscode.commands.executeCommand('workbench.action.chat.open', { query: prompt });
        } else if (message.command === 'openFile') {
            revealFile(message.filePath, vscode.ViewColumn.One, message.location.line, message.location.character);
        } else if (message.command === 'showInfoMessage') {
            void vscode.window.showInformationMessage(message.text);
        } else if (message.command === 'showVariableValue') {
            const valStr = this.checkResult ? this.checkResult.formatValue(message.valueId) : undefined;
            if (valStr) {
                createDocument(valStr);
            }
        }
    }

    private getWebviewContent() {
        const webview = this.panel.webview;
        const webviewUri = getUri(webview, this.extensionUri, ['out', 'check-result-view.js']);
        const styleUri = getUri(webview, this.extensionUri, ['out', 'check-result-view.css']);
        const nonce = getNonce();

        return /*html*/ `
        <!DOCTYPE html>
        <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource}; font-src ${webview.cspSource}; script-src 'nonce-${nonce}';">
                <link rel="stylesheet" href="${styleUri}">
                <title>Model checking</title>
            </head>
            <body>
                <div id="root"></div>
                <script type="module" nonce="${nonce}" src="${webviewUri}"></script>
            </body>
        </html>
        `;
    }
}
