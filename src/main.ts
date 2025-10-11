import * as vscode from 'vscode';
import {
    CMD_CHECK_MODEL_RUN, CMD_CHECK_MODEL_STOP, CMD_CHECK_MODEL_DISPLAY, CMD_SHOW_TLC_OUTPUT,
    CMD_CHECK_MODEL_CUSTOM_RUN, checkModel, displayModelChecking, stopModelChecking,
    showTlcOutput, checkModelCustom, CMD_CHECK_MODEL_RUN_AGAIN, runLastCheckAgain,
    setCoverageProvider
} from './commands/checkModel';
import { CMD_RUN_REPL, launchRepl, REPLTerminalProfileProvider } from './commands/runRepl';
import { TLAPLUS_DEBUG_LAUNCH_CHECKNDEBUG, TLAPLUS_DEBUG_LAUNCH_CUSTOMCHECKNDEBUG, TLAPLUS_DEBUG_LAUNCH_DEBUG,
    TLAPLUS_DEBUG_LAUNCH_SMOKE,TLADebugAdapterServerDescriptorFactory, checkAndDebugSpec,
    checkAndDebugSpecCustom, attachDebugger, smokeTestSpec
} from './debugger/debugging';
import { CMD_EVALUATE_SELECTION, evaluateSelection, CMD_EVALUATE_EXPRESSION,
    evaluateExpression } from './commands/evaluateExpression';
import { parseModule, CMD_PARSE_MODULE } from './commands/parseModule';
import { visualizeTlcOutput, CMD_VISUALIZE_TLC_OUTPUT } from './commands/visualizeOutput';
import { visualizeCoverage, CMD_VISUALIZE_COVERAGE } from './commands/visualizeCoverage';
import { exportModuleToTex, exportModuleToPdf, CMD_EXPORT_TLA_TO_TEX,
    CMD_EXPORT_TLA_TO_PDF } from './commands/exportModule';
import { TlaOnTypeFormattingEditProvider } from './formatters/tla';
import { CfgOnTypeFormattingEditProvider } from './formatters/cfg';
import { TlaCodeActionProvider } from './actions';
import { TlaDocumentSymbolsProvider } from './symbols/tlaSymbols';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG } from './common';
import { TlaCompletionItemProvider } from './completions/tlaCompletions';
import { CfgCompletionItemProvider } from './completions/cfgCompletions';
import { TlaDeclarationsProvider, TlaDefinitionsProvider } from './declarations/tlaDeclarations';
import { TlaDocumentInfos } from './model/documentInfo';
import { syncTlcStatisticsSetting, listenTlcStatConfigurationChanges } from './commands/tlcStatisticsCfg';
import { TlapsClient } from './tlaps';
import { CurrentProofStepWebviewViewProvider } from './panels/currentProofStepWebviewViewProvider';
import { moduleSearchPaths } from './paths';
import { ModuleSearchPathsTreeDataProvider } from './panels/moduleSearchPathsTreeDataProvider';
import { CheckModuleTool, ExploreModuleTool, SmokeModuleTool } from './lm/TLCTool';
import { ParseModuleTool, SymbolProviderTool } from './lm/SANYTool';
import { MCPServer } from './lm/MCPServer';
import { TlcCoverageDecorationProvider } from './tlcCoverage';
import { registerCoverageCommands } from './commands/toggleCoverage';
import { JarFileSystemProvider } from './JarFileSystemProvider';

const TLAPLUS_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS };
const TLAPLUS_CFG_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS_CFG };

const tlaDocInfos = new TlaDocumentInfos();

// Holds all the error messages
let diagnostic: vscode.DiagnosticCollection;

// Export function to access the diagnostic collection
export function getDiagnostic(): vscode.DiagnosticCollection {
    return diagnostic;
}

let tlapsClient: TlapsClient | undefined;

/**
 * Extension entry point.
 */
export async function activate(context: vscode.ExtensionContext): Promise<void> {
    moduleSearchPaths.setup(context);

    const jarFileSystemProvider = new JarFileSystemProvider();
    context.subscriptions.push(
        jarFileSystemProvider,
        vscode.workspace.registerFileSystemProvider('jarfile', jarFileSystemProvider, {
            isReadonly: true
        }),
        vscode.workspace.onDidOpenTextDocument((document) => {
            if (document.uri.scheme === 'jarfile' && document.languageId !== LANG_TLAPLUS) {
                void vscode.languages.setTextDocumentLanguage(document, LANG_TLAPLUS);
            }
        })
    );

    const currentProofStepWebviewViewProvider = new CurrentProofStepWebviewViewProvider(context.extensionUri);
    diagnostic = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
    context.subscriptions.push(
        vscode.workspace.onDidDeleteFiles((event) => {
            event.files.forEach((uri) => {
                // Clear diagnostics for deleted TLA+ files
                // Note: We can't check languageId for deleted files, so we use file extension
                if (uri.fsPath.endsWith('.tla')) {
                    diagnostic.delete(uri);
                }
            });
        }),
        vscode.workspace.onDidRenameFiles((event) => {
            event.files.forEach((rename) => {
                // Clear diagnostics for the old file path when TLA+ files are renamed
                // Note: We can't check languageId for the old URI, so we use file extension
                if (rename.oldUri.fsPath.endsWith('.tla')) {
                    diagnostic.delete(rename.oldUri);
                }
            });
        }),
        vscode.workspace.onDidSaveTextDocument((document) => {
            // Clear diagnostics if the document is empty after being saved.
            if (document.getText().trim() === '' &&
                document.languageId === LANG_TLAPLUS) {
                diagnostic.delete(document.uri);
            }
        }),
        vscode.commands.registerCommand(
            CMD_PARSE_MODULE,
            () => parseModule(diagnostic)),
        vscode.commands.registerCommand(
            CMD_EXPORT_TLA_TO_TEX,
            () => exportModuleToTex(context)),
        vscode.commands.registerCommand(
            CMD_EXPORT_TLA_TO_PDF,
            () => exportModuleToPdf(context)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_RUN,
            (uri) => checkModel(uri, diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_RUN_AGAIN,
            () => runLastCheckAgain(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_CUSTOM_RUN,
            () => checkModelCustom(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_SHOW_TLC_OUTPUT,
            () => showTlcOutput()),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_STOP,
            () => stopModelChecking()),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_DISPLAY,
            () => displayModelChecking(context)),
        vscode.commands.registerCommand(
            CMD_VISUALIZE_TLC_OUTPUT,
            () => visualizeTlcOutput(context)),
        vscode.commands.registerCommand(
            CMD_VISUALIZE_COVERAGE,
            (uri: vscode.Uri) => visualizeCoverage(uri, context)),
        vscode.commands.registerCommand(
            CMD_EVALUATE_SELECTION,
            () => evaluateSelection(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_EVALUATE_EXPRESSION,
            () => evaluateExpression(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_RUN_REPL,
            () => launchRepl()),
        vscode.window.registerTerminalProfileProvider(
            CMD_RUN_REPL,
            new REPLTerminalProfileProvider()),
        vscode.languages.registerCodeActionsProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaCodeActionProvider(),
            { providedCodeActionKinds: [vscode.CodeActionKind.Source] }),
        vscode.debug.registerDebugAdapterDescriptorFactory(
            LANG_TLAPLUS,
            new TLADebugAdapterServerDescriptorFactory()),
        vscode.languages.registerOnTypeFormattingEditProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaOnTypeFormattingEditProvider(),
            '\n', 'd', 'e', 'f', 'r'),
        vscode.languages.registerOnTypeFormattingEditProvider(
            TLAPLUS_CFG_FILE_SELECTOR,
            new CfgOnTypeFormattingEditProvider(),
            '\n'),
        vscode.languages.registerDocumentSymbolProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaDocumentSymbolsProvider(tlaDocInfos),
            { label: 'TLA+' }),
        vscode.languages.registerCompletionItemProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaCompletionItemProvider(tlaDocInfos)),
        vscode.languages.registerCompletionItemProvider(
            TLAPLUS_CFG_FILE_SELECTOR,
            new CfgCompletionItemProvider()),
        vscode.languages.registerDeclarationProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaDeclarationsProvider(tlaDocInfos)
        ),
        vscode.languages.registerDefinitionProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaDefinitionsProvider(tlaDocInfos)
        ),
        vscode.commands.registerCommand(
            TLAPLUS_DEBUG_LAUNCH_CHECKNDEBUG,
            (uri) => checkAndDebugSpec(uri, diagnostic, context)
        ),
        vscode.commands.registerCommand(
            TLAPLUS_DEBUG_LAUNCH_CUSTOMCHECKNDEBUG,
            (uri) => checkAndDebugSpecCustom(uri, diagnostic, context)
        ),
        vscode.commands.registerCommand(
            TLAPLUS_DEBUG_LAUNCH_SMOKE,
            (uri) => smokeTestSpec(uri, diagnostic, context)
        ),
        vscode.commands.registerCommand(
            TLAPLUS_DEBUG_LAUNCH_DEBUG,
            (uri) => attachDebugger()
        ),
        vscode.languages.registerEvaluatableExpressionProvider(
            TLAPLUS_FILE_SELECTOR, {
            // https://github.com/microsoft/vscode/issues/89084
            // https://github.com/microsoft/vscode/issues/24520
            // https://github.com/microsoft/vscode-mock-debug/blob/ (stupid linter!)
            // 393ee2b2443e270bacd9f11fa219c39a88fc987d/src/extension.ts#L63-L84
            // Also see wordPattern in tlaplus-lang-config.json that drops "@"
            // and "'" compared to VSCode's standard wordPattern.
            // https://github.com/tlaplus/vscode-tlaplus/issues/200
                provideEvaluatableExpression(document: vscode.TextDocument, position: vscode.Position):
                    vscode.ProviderResult<vscode.EvaluatableExpression> {
                    const wordRange = document.getWordRangeAtPosition(position);
                    return wordRange ? new vscode.EvaluatableExpression(wordRange,
                        encodeURI(
                            'tlaplus://' + document.uri + '?' + document.getText(wordRange) + '#' +
                            (wordRange.start.line + 1) + ' ' +
                            (wordRange.start.character + 1) + ' ' +
                            (wordRange.end.line + 1) + ' ' +
                            // For SANY, the location of the first character in a file is:
                            //   1 1 1 1
                            // whereas VSCode defines it to be:
                            //   1 1 1 2
                            (wordRange.end.character /** + 1 */))) : undefined;
                }
            }
        ),
        vscode.window.registerWebviewViewProvider(
            CurrentProofStepWebviewViewProvider.viewType,
            currentProofStepWebviewViewProvider,
        ),
        vscode.window.registerTreeDataProvider(
            ModuleSearchPathsTreeDataProvider.viewType,
            new ModuleSearchPathsTreeDataProvider(context)
        ),
        vscode.lm.registerTool(
            'chat-tools-tlaplus_sany_parse',
            new ParseModuleTool()
        ),
        vscode.lm.registerTool(
            'chat-tools-tlaplus_sany_symbol',
            new SymbolProviderTool()
        ),
        vscode.lm.registerTool(
            'chat-tools-tlaplus_tlc_smoke',
            new SmokeModuleTool()
        ),
        vscode.lm.registerTool(
            'chat-tools-tlaplus_tlc_explore',
            new ExploreModuleTool()
        ),
        vscode.lm.registerTool(
            'chat-tools-tlaplus_tlc_check',
            new CheckModuleTool()
        )
    );
    tlapsClient = new TlapsClient(
        context,
        details => currentProofStepWebviewViewProvider.showProofStepDetails(details),
        configChanged => currentProofStepWebviewViewProvider.considerConfigChanged(configChanged)
    );

    // Initialize coverage provider
    const coverageProvider = new TlcCoverageDecorationProvider(context);
    context.subscriptions.push(coverageProvider);
    setCoverageProvider(coverageProvider);

    // Register coverage commands
    registerCoverageCommands(context, coverageProvider);

    // Start MCP server - unconditionally in Cursor (AI-first IDE), or based on port configuration in VSCode
    if (vscode.env.appName?.toLowerCase().includes('cursor')) {
        const p = vscode.workspace.getConfiguration().get<number>('tlaplus.mcp.port');
        if (typeof p === 'number' && p === -1) {
            await vscode.workspace.getConfiguration().update('tlaplus.mcp.port', 0, vscode.ConfigurationTarget.Global);
        }
    }
    const mcpPort = vscode.workspace.getConfiguration().get<number>('tlaplus.mcp.port');
    if (typeof mcpPort === 'number' && (mcpPort >= 1024 && mcpPort <= 65535 || mcpPort === 0)) {
        const tlaMcpServer = new MCPServer(mcpPort);
        context.subscriptions.push(tlaMcpServer);

        // TODO : At this point, we would like to programmatically register the MCP server in Cursor
        // without creating a permanent file.  A permanent file, i.e., static configuration makes sense for
        // an external MCP server, but not for the transient MCP server that is started by the extension.
    }
    syncTlcStatisticsSetting()
        .catch((err) => console.error(err))
        .then(() => listenTlcStatConfigurationChanges(context.subscriptions));
}

export function deactivate() {
    if (tlapsClient) {
        tlapsClient.deactivate();
    }
    tlapsClient = undefined;
}
