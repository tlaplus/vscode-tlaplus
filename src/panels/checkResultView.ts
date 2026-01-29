import * as vscode from 'vscode';
import { CMD_CHECK_MODEL_RUN_AGAIN, CMD_CHECK_MODEL_STOP, CMD_SHOW_TLC_OUTPUT } from '../commands/checkModel';
import { ModelCheckResult, ModelCheckResultSource } from '../model/check';
import { getNonce } from './utilities/getNonce';
import { getUri } from './utilities/getUri';
import { createDocument, revealFile } from './utilities/workspace';
import { TLAPLUS_DEBUG_LOAD_TRACE } from '../debugger/debugging';

export function updateCheckResultView(checkResult: ModelCheckResult): void {
    CheckResultViewPanel.updateCheckResult(checkResult);
}

export function revealEmptyCheckResultView(extContext: vscode.ExtensionContext): void {
    CheckResultViewPanel.renderEmpty(extContext.extensionUri);
}

export function revealLastCheckResultView(extContext: vscode.ExtensionContext): void {
    CheckResultViewPanel.renderLastResult(extContext.extensionUri);
}

export function isCheckResultViewPanelFocused(): boolean {
    return CheckResultViewPanel.isPanelFocused();
}

class CheckResultViewPanel {
    private static readonly viewType = 'modelChecking';
    private static currentPanel: CheckResultViewPanel | undefined;
    private static lastCheckResult: ModelCheckResult | undefined;

    private readonly panel: vscode.WebviewPanel;
    private readonly extensionUri: vscode.Uri;
    private readonly disposables: vscode.Disposable[] = [];
    private checkResult: ModelCheckResult;

    private constructor(extensionUri: vscode.Uri) {
        this.extensionUri = extensionUri;
        this.checkResult = ModelCheckResult.createEmpty(ModelCheckResultSource.Process);

        const preserveFocus = vscode.workspace.getConfiguration()
            .get<boolean>('tlaplus.tlc.modelChecker.preserveEditorFocus');

        this.panel = vscode.window.createWebviewPanel(
            CheckResultViewPanel.viewType,
            'TLA+ model checking',
            { viewColumn: vscode.ViewColumn.Beside, preserveFocus: preserveFocus },
            {
                enableScripts: true,
                retainContextWhenHidden: true,
                localResourceRoots: [vscode.Uri.joinPath(extensionUri, 'out')]
            }
        );

        this.panel.iconPath = {
            dark: vscode.Uri.joinPath(extensionUri, 'resources','images','preview-dark.svg'),
            light: vscode.Uri.joinPath(extensionUri, 'resources','images','preview-light.svg'),
        };

        // Set an event listener to listen for when the panel is disposed
        this.panel.onDidDispose(() => this.dispose(), null, this.disposables);

        // Set the HTML content for the webview panel
        this.panel.webview.html = this.getWebviewContent();

        // Set message listener
        this.panel.webview.onDidReceiveMessage((message) => this.handleWebviewMessage(message));
    }

    public static updateCheckResult(checkResult: ModelCheckResult) {
        CheckResultViewPanel.lastCheckResult = checkResult;
        if (CheckResultViewPanel.currentPanel) {
            CheckResultViewPanel.currentPanel.updateView(checkResult);
        }
    }

    public static isPanelFocused(): boolean {
        return CheckResultViewPanel.currentPanel?.panel.active === true;
    }

    public static renderEmpty(extensionUri: vscode.Uri) {
        const preserveFocus = vscode.workspace.getConfiguration()
            .get<boolean>('tlaplus.tlc.modelChecker.preserveEditorFocus');
        const previousEditor = preserveFocus ? vscode.window.activeTextEditor : undefined;
        if (!CheckResultViewPanel.currentPanel) {
            CheckResultViewPanel.currentPanel = new CheckResultViewPanel(extensionUri);
        }

        this.updateCheckResult(ModelCheckResult.createEmpty(ModelCheckResultSource.Process));
        CheckResultViewPanel.currentPanel.panel.reveal(undefined, preserveFocus);
        if (preserveFocus && previousEditor) {
            void vscode.window.showTextDocument(previousEditor.document, previousEditor.viewColumn, true);
        }
    }

    public static renderLastResult(extensionUri: vscode.Uri) {
        const preserveFocus = vscode.workspace.getConfiguration()
            .get<boolean>('tlaplus.tlc.modelChecker.preserveEditorFocus');
        const previousEditor = preserveFocus ? vscode.window.activeTextEditor : undefined;
        if (!CheckResultViewPanel.currentPanel) {
            CheckResultViewPanel.currentPanel = new CheckResultViewPanel(extensionUri);
        }

        const lastModelResult = CheckResultViewPanel.lastCheckResult
            ? CheckResultViewPanel.lastCheckResult
            : ModelCheckResult.createEmpty(ModelCheckResultSource.Process);

        this.updateCheckResult(lastModelResult);
        CheckResultViewPanel.currentPanel.panel.reveal(undefined, preserveFocus);
        if (preserveFocus && previousEditor) {
            void vscode.window.showTextDocument(previousEditor.document, previousEditor.viewColumn, true);
        }
    }

    private updateView(checkResult: ModelCheckResult) {
        this.checkResult = checkResult;
        this.panel.webview.postMessage({
            checkResult: checkResult
        });
    }

    private dispose() {
        CheckResultViewPanel.currentPanel = undefined;

        // Dispose of the current webview panel
        this.panel.dispose();

        // Dispose of all disposables (i.e. commands) associated with the current webview panel
        while (this.disposables.length) {
            const disposable = this.disposables.pop();
            if (disposable) {
                disposable.dispose();
            }
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
                // Format state number and title
                stateLines.push(`${traceItem.num}: <${traceItem.title}>`);
                
                // Format variables - use format('') for better multi-line formatting
                if (traceItem.variables && traceItem.variables.items) {
                    for (const variable of traceItem.variables.items) {
                        const formattedValue = variable.format('');
                        stateLines.push(`/\\ ${variable.key} = ${formattedValue}`);
                    }
                }
                
                // Add empty line between states
                stateLines.push('');
            }
            
            traces.push(stateLines.join('\n'));
        }
        
        return traces.join('\n---\n\n') || 'No counterexample available.';
    }

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    private handleWebviewMessage(message: any) {
        if (message.command === 'stop') {
            vscode.commands.executeCommand(CMD_CHECK_MODEL_STOP);
        } else if (message.command === 'showTlcOutput') {
            vscode.commands.executeCommand(CMD_SHOW_TLC_OUTPUT);
        } else if (message.command === 'runAgain') {
            vscode.commands.executeCommand(CMD_CHECK_MODEL_RUN_AGAIN);
        } else if (message.command === 'debugCounterexample') {
            // Get the TLA file path from the current check result
            const specFiles = this.checkResult?.specFiles;
            if (specFiles && typeof specFiles === 'object' && 'tlaFilePath' in specFiles) {
                vscode.commands.executeCommand(TLAPLUS_DEBUG_LOAD_TRACE, specFiles.tlaFilePath);
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
            
            vscode.commands.executeCommand('workbench.action.chat.open', { query: prompt });
        } else if (message.command === 'openFile') {
            // `One` is used here because at the moment, VSCode doesn't provide API
            // for revealing existing document, so we're speculating here to reduce open documents duplication.
            revealFile(message.filePath, vscode.ViewColumn.One, message.location.line, message.location.character);
        } else if (message.command === 'showInfoMessage') {
            vscode.window.showInformationMessage(message.text);
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

        // Tip: Install the es6-string-html VS Code extension to enable code highlighting below
        /* eslint-disable max-len */
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
