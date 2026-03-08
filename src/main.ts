import * as vscode from 'vscode';
import {
    CMD_CHECK_MODEL_RUN, CMD_CHECK_MODEL_STOP, CMD_CHECK_MODEL_DISPLAY, CMD_SHOW_TLC_OUTPUT,
    CMD_CHECK_MODEL_CUSTOM_RUN, checkModel, displayModelChecking, stopModelChecking,
    showTlcOutput, checkModelCustom, CMD_CHECK_MODEL_RUN_AGAIN, runLastCheckAgain,
    CTX_TLC_CAN_RUN_AGAIN, CTX_TLC_RUNNING,
} from './commands/checkModel';
import { CMD_RUN_REPL, launchRepl, REPLTerminalProfileProvider } from './commands/runRepl';
import {
    TLAPLUS_DEBUG_LAUNCH_CHECKNDEBUG, TLAPLUS_DEBUG_LAUNCH_CUSTOMCHECKNDEBUG, TLAPLUS_DEBUG_LAUNCH_DEBUG,
    TLAPLUS_DEBUG_LAUNCH_SMOKE, TLAPLUS_DEBUG_GOTO_STATE, TLAPLUS_DEBUG_LOAD_TRACE, TLADebugAdapterServerDescriptorFactory,
    TLADebugAdapterTrackerFactory, checkAndDebugSpec, checkAndDebugSpecCustom, attachDebugger, smokeTestSpec, gotoState,
    debugCounterexample,
} from './debugger/debugging';
import { CMD_EVALUATE_SELECTION, evaluateSelection, CMD_EVALUATE_EXPRESSION, evaluateExpression } from './commands/evaluateExpression';
import { parseModule, CMD_PARSE_MODULE } from './commands/parseModule';
import { visualizeTlcOutput, CMD_VISUALIZE_TLC_OUTPUT } from './commands/visualizeOutput';
import { visualizeCoverage, CMD_VISUALIZE_COVERAGE } from './commands/visualizeCoverage';
import { exportModuleToTex, exportModuleToPdf, CMD_EXPORT_TLA_TO_TEX, CMD_EXPORT_TLA_TO_PDF } from './commands/exportModule';
import { TlaOnTypeFormattingEditProvider } from './formatters/tla';
import { CfgOnTypeFormattingEditProvider } from './formatters/cfg';
import { registerDocumentFormatter } from './formatters/tlaFormatter';
import { TlaCodeActionProvider } from './actions';
import { TlaDocumentSymbolsProvider } from './symbols/tlaSymbols';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG } from './common';
import { TlaCompletionItemProvider } from './completions/tlaCompletions';
import { CfgCompletionItemProvider } from './completions/cfgCompletions';
import { TlaDeclarationsProvider, TlaDefinitionsProvider } from './declarations/tlaDeclarations';
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
import { acquireJarFileSystemProvider } from './JarFileSystemProvider';
import { createExtensionRuntime } from './runtime/extensionRuntime';
import { CheckResultViewController } from './panels/checkResultView';
import { CheckSession } from './services/checkService';

const TLAPLUS_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS };
const TLAPLUS_CFG_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS_CFG };

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    moduleSearchPaths.setup(context);

    const diagnosticCollection = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
    const runtime = createExtensionRuntime(diagnosticCollection);
    const checkResultView = new CheckResultViewController(context.extensionUri);
    const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);

    const jarProviderHandle = acquireJarFileSystemProvider();
    const currentProofStepWebviewViewProvider = new CurrentProofStepWebviewViewProvider(context.extensionUri);
    const coverageProvider = new TlcCoverageDecorationProvider(context);

    const updateCoverage = (session: CheckSession): void => {
        const checkResult = session.result;
        if (!checkResult || checkResult.coverageStat.length === 0) {
            return;
        }
        let totalDistinctStates = 0;
        if (checkResult.initialStatesStat.length > 0) {
            const lastStat = checkResult.initialStatesStat[checkResult.initialStatesStat.length - 1];
            totalDistinctStates = lastStat.distinct;
        }
        coverageProvider.updateCoverage(checkResult.coverageStat, totalDistinctStates);
    };

    const updateTlcUiState = (): void => {
        const activeSession = runtime.checkService.sessions.latestActive();
        const lastSpecFiles = runtime.checkService.sessions.lastSpecFiles();
        const active = !!activeSession;
        statusBarItem.text = 'TLC' + (active
            ? (activeSession ? ` (Model: ${activeSession.specFiles.modelName})` : '') + ' $(gear~spin)'
            : '');
        statusBarItem.tooltip = 'TLA+ model checking' + (active
            ? (activeSession ? ` of model ${activeSession.specFiles.modelName}` : '') + ' is running'
            : ' result');
        statusBarItem.command = CMD_CHECK_MODEL_DISPLAY;
        statusBarItem.show();
        void vscode.commands.executeCommand('setContext', CTX_TLC_RUNNING, active);
        void vscode.commands.executeCommand('setContext', CTX_TLC_CAN_RUN_AGAIN, !!lastSpecFiles);
    };

    runtime.checkService.onDidUpdateSession((session) => {
        if (session.result) {
            checkResultView.updateCheckResult(session.result);
            updateCoverage(session);
        }
        updateTlcUiState();
    });
    runtime.checkService.onDidFinishSession((session) => {
        runtime.diagnosticsProjector.project(session.diagnostics);
        updateTlcUiState();
    });

    const tlapsClient = new TlapsClient(
        context,
        details => currentProofStepWebviewViewProvider.showProofStepDetails(details),
        configChanged => currentProofStepWebviewViewProvider.considerConfigChanged(configChanged)
    );

    context.subscriptions.push(
        diagnosticCollection,
        runtime.checkService,
        checkResultView,
        statusBarItem,
        coverageProvider,
        jarProviderHandle,
        { dispose: () => tlapsClient.deactivate() },
        vscode.workspace.onDidOpenTextDocument((document) => {
            if (document.uri.scheme === 'jarfile' && document.languageId !== LANG_TLAPLUS) {
                void vscode.languages.setTextDocumentLanguage(document, LANG_TLAPLUS);
            }
        }),
        vscode.workspace.onDidDeleteFiles((event) => {
            event.files.forEach((uri) => {
                if (uri.fsPath.endsWith('.tla')) {
                    runtime.diagnosticsProjector.delete(uri);
                    runtime.semanticService.clear(uri);
                }
            });
        }),
        vscode.workspace.onDidRenameFiles((event) => {
            event.files.forEach((rename) => {
                if (rename.oldUri.fsPath.endsWith('.tla')) {
                    runtime.diagnosticsProjector.delete(rename.oldUri);
                    runtime.semanticService.clear(rename.oldUri);
                }
            });
        }),
        vscode.workspace.onDidSaveTextDocument((document) => {
            if (document.languageId === LANG_TLAPLUS && document.getText().trim() === '') {
                runtime.diagnosticsProjector.delete(document.uri);
            }
        }),
        vscode.commands.registerCommand(CMD_PARSE_MODULE, () => parseModule(runtime)),
        vscode.commands.registerCommand(CMD_EXPORT_TLA_TO_TEX, () => exportModuleToTex(context)),
        vscode.commands.registerCommand(CMD_EXPORT_TLA_TO_PDF, () => exportModuleToPdf(context)),
        vscode.commands.registerCommand(CMD_CHECK_MODEL_RUN, (uri) => checkModel(uri, runtime, context, checkResultView)),
        vscode.commands.registerCommand(CMD_CHECK_MODEL_RUN_AGAIN, () => runLastCheckAgain(runtime, context, checkResultView)),
        vscode.commands.registerCommand(CMD_CHECK_MODEL_CUSTOM_RUN, () => checkModelCustom(runtime, context, checkResultView)),
        vscode.commands.registerCommand(CMD_SHOW_TLC_OUTPUT, () => showTlcOutput(runtime)),
        vscode.commands.registerCommand(CMD_CHECK_MODEL_STOP, () => stopModelChecking(runtime)),
        vscode.commands.registerCommand(CMD_CHECK_MODEL_DISPLAY, () => displayModelChecking(checkResultView)),
        vscode.commands.registerCommand(CMD_VISUALIZE_TLC_OUTPUT, () => visualizeTlcOutput(context, checkResultView)),
        vscode.commands.registerCommand(CMD_VISUALIZE_COVERAGE, (uri: vscode.Uri) => visualizeCoverage(uri, context)),
        vscode.commands.registerCommand(CMD_EVALUATE_SELECTION, () => evaluateSelection(runtime, context, checkResultView)),
        vscode.commands.registerCommand(CMD_EVALUATE_EXPRESSION, () => evaluateExpression(runtime, context, checkResultView)),
        vscode.commands.registerCommand(CMD_RUN_REPL, () => launchRepl()),
        vscode.window.registerTerminalProfileProvider(CMD_RUN_REPL, new REPLTerminalProfileProvider()),
        vscode.languages.registerCodeActionsProvider(TLAPLUS_FILE_SELECTOR, new TlaCodeActionProvider(), {
            providedCodeActionKinds: [vscode.CodeActionKind.Source],
        }),
        vscode.debug.registerDebugAdapterDescriptorFactory(LANG_TLAPLUS, new TLADebugAdapterServerDescriptorFactory()),
        vscode.debug.registerDebugAdapterTrackerFactory(LANG_TLAPLUS, new TLADebugAdapterTrackerFactory()),
        vscode.languages.registerOnTypeFormattingEditProvider(TLAPLUS_FILE_SELECTOR, new TlaOnTypeFormattingEditProvider(), '\n', 'd', 'e', 'f', 'r'),
        vscode.languages.registerOnTypeFormattingEditProvider(TLAPLUS_CFG_FILE_SELECTOR, new CfgOnTypeFormattingEditProvider(), '\n'),
        vscode.languages.registerDocumentSymbolProvider(TLAPLUS_FILE_SELECTOR, new TlaDocumentSymbolsProvider(runtime.semanticService), { label: 'TLA+' }),
        vscode.languages.registerCompletionItemProvider(TLAPLUS_FILE_SELECTOR, new TlaCompletionItemProvider(runtime.semanticService)),
        vscode.languages.registerCompletionItemProvider(TLAPLUS_CFG_FILE_SELECTOR, new CfgCompletionItemProvider()),
        vscode.languages.registerDeclarationProvider(TLAPLUS_FILE_SELECTOR, new TlaDeclarationsProvider(runtime.semanticService)),
        vscode.languages.registerDefinitionProvider(TLAPLUS_FILE_SELECTOR, new TlaDefinitionsProvider(runtime.semanticService)),
        vscode.commands.registerCommand(TLAPLUS_DEBUG_LAUNCH_CHECKNDEBUG, (uri) => checkAndDebugSpec(uri, runtime, context, checkResultView)),
        vscode.commands.registerCommand(TLAPLUS_DEBUG_LAUNCH_CUSTOMCHECKNDEBUG, (uri) => checkAndDebugSpecCustom(uri, runtime, context, checkResultView)),
        vscode.commands.registerCommand(TLAPLUS_DEBUG_LAUNCH_SMOKE, (uri) => smokeTestSpec(uri, runtime, context, checkResultView)),
        vscode.commands.registerCommand(TLAPLUS_DEBUG_LAUNCH_DEBUG, () => attachDebugger()),
        vscode.commands.registerCommand(TLAPLUS_DEBUG_GOTO_STATE, (debugContext) => gotoState(debugContext)),
        vscode.commands.registerCommand(TLAPLUS_DEBUG_LOAD_TRACE, (tlaFilePath) => debugCounterexample(tlaFilePath, runtime, context, checkResultView)),
        vscode.languages.registerEvaluatableExpressionProvider(TLAPLUS_FILE_SELECTOR, {
            provideEvaluatableExpression(document: vscode.TextDocument, position: vscode.Position): vscode.ProviderResult<vscode.EvaluatableExpression> {
                const wordRange = document.getWordRangeAtPosition(position);
                return wordRange ? new vscode.EvaluatableExpression(wordRange,
                    encodeURI(
                        'tlaplus://' + document.uri + '?' + document.getText(wordRange) + '#' +
                        (wordRange.start.line + 1) + ' ' +
                        (wordRange.start.character + 1) + ' ' +
                        (wordRange.end.line + 1) + ' ' +
                        (wordRange.end.character))) : undefined;
            }
        }),
        vscode.window.registerWebviewViewProvider(CurrentProofStepWebviewViewProvider.viewType, currentProofStepWebviewViewProvider),
        vscode.window.registerTreeDataProvider(ModuleSearchPathsTreeDataProvider.viewType, new ModuleSearchPathsTreeDataProvider(context)),
        vscode.lm.registerTool('chat-tools-tlaplus_sany_parse', new ParseModuleTool(runtime.parseService, runtime.diagnosticsProjector)),
        vscode.lm.registerTool('chat-tools-tlaplus_sany_symbol', new SymbolProviderTool(runtime.semanticService)),
        vscode.lm.registerTool('chat-tools-tlaplus_tlc_smoke', new SmokeModuleTool(runtime.checkService)),
        vscode.lm.registerTool('chat-tools-tlaplus_tlc_explore', new ExploreModuleTool(runtime.checkService)),
        vscode.lm.registerTool('chat-tools-tlaplus_tlc_check', new CheckModuleTool(runtime.checkService)),
    );

    registerCoverageCommands(context, coverageProvider);

    const mcpPort = vscode.workspace.getConfiguration().get<number>('tlaplus.mcp.port');
    if (typeof mcpPort === 'number' && ((mcpPort >= 1024 && mcpPort <= 65535) || mcpPort === 0)) {
        context.subscriptions.push(new MCPServer(mcpPort, runtime));
    }

    syncTlcStatisticsSetting()
        .catch((err) => console.error(err))
        .then(() => listenTlcStatConfigurationChanges(context.subscriptions));

    registerDocumentFormatter(context);
    updateTlcUiState();
}

export function deactivate(): void {
}
