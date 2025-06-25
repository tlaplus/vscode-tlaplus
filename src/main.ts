import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { createHash } from 'crypto';
import { spawn } from 'child_process';

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
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG, exists, readFile, writeFile } from './common';
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

const TLAPLUS_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS };
const TLAPLUS_CFG_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS_CFG };
const CHANGELOG_URL = vscode.Uri.parse('https://github.com/tlaplus/vscode-tlaplus/blob/master/CHANGELOG.md#change-log');

const tlaDocInfos = new TlaDocumentInfos();

// Holds all the error messages
let diagnostic: vscode.DiagnosticCollection;

let tlapsClient: TlapsClient | undefined;

/**
 * Extension entry point.
 */
export async function activate(context: vscode.ExtensionContext): Promise<void> {
    moduleSearchPaths.setup(context);

    const currentProofStepWebviewViewProvider = new CurrentProofStepWebviewViewProvider(context.extensionUri);
    diagnostic = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
    context.subscriptions.push(
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
    showChangeLog(context.extensionPath)
        .catch((err) => console.error(err));

    context.subscriptions.push(
        vscode.languages.registerDocumentFormattingEditProvider('tlaplus', {
            provideDocumentFormattingEdits(document: vscode.TextDocument): vscode.ProviderResult<vscode.TextEdit[]> {
                return new Promise((resolve, reject) => {
                    const inputText = document.getText();
                    // need the module name to create the file. The filename should match the module name.
                    const moduleName = extractModuleName(inputText);
                    // create a unique temp folder.
                    const md5Hash = generateHash(inputText, 'md5');
                    const tempDir = path.join(context.globalStorageUri.fsPath, md5Hash);

                    // create folder if not exists
                    try {
                        fs.mkdirSync(tempDir);
                    } catch (err) {
                        if ((err as NodeJS.ErrnoException).code !== 'EEXIST') {
                            reject(err);
                        }
                    }

                    let tempInputPath = path.join(context.globalStorageUri.fsPath, md5Hash,  moduleName + '.tla');
                    const tempOutputPath = path.join(context.globalStorageUri.fsPath, md5Hash, moduleName + '.tla');
                    // Write input text to temporary file
                    fs.writeFileSync(tempInputPath, inputText);

                    // if this is a real file, use as input the actual file.
                    // this is needed because SANY needs to parse also the EXTENDed modules...
                    // TODO: fails if EXTENDS TLAPS.
                    if(document.uri.scheme === "file") {
                        tempInputPath = document.uri.fsPath;
                    }
                    // Execute the Java formatter

                    // Execute the Java formatter using spawn
                    const javaProcess = spawn('java', ['-jar', '/home/fponzi/dev/tla+/tlaplus-formatter/build/libs/tlaplus-formatter.jar', '-v', 'ERROR', tempInputPath, tempInputPath]);
                    // Capture and log standard output
                    javaProcess.stdout.on('data', (data) => {
                        console.log(`STDOUT: ${data}`);
                    });

                    // Capture and log standard error
                    javaProcess.stderr.on('data', (data) => {
                        console.error(`STDERR: ${data}`);
                    });

                    javaProcess.on('error', (error) => {
                        vscode.window.showErrorMessage(`Formatter failed: ${error.message}`);
                        reject(error);
                    });

                    javaProcess.on('close', (code) => {
                        if (code !== 0) {
                            vscode.window.showErrorMessage(`Formatter failed with exit code ${code}`);
                            return reject(new Error(`Formatter failed with exit code ${code}`));
                        }
                        // Read the formatted text
                        const formattedText = fs.readFileSync(tempOutputPath, 'utf8');
                        const edit = [vscode.TextEdit.replace(new vscode.Range(0, 0, document.lineCount, 0), formattedText)];
                        fs.rmSync(tempDir, { recursive: true, force: true });
                        resolve(edit);
                    });
                });
            }
        })
    );

    // Register a command to manually trigger formatting
    const disposable = vscode.commands.registerCommand('extension.formatDocument', () => {
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            vscode.commands.executeCommand('editor.action.formatDocument');
        }
    });

    context.subscriptions.push(disposable);
}

function generateHash(input: string, algorithm: string): string {
    const hash = createHash(algorithm);
    hash.update(input);
    return hash.digest('hex');
}
function extractModuleName(text: string): string | null {
    const regex = /MODULE\s+(\w+)/;
    const match = regex.exec(text);
    if (match && match[1]) {
        return match[1];
    }
    return null;
}


export function deactivate() {
    if (tlapsClient) {
        tlapsClient.deactivate();
    }
    tlapsClient = undefined;
}

async function showChangeLog(extPath: string) {
    const pkgData = await readFile(`${extPath}${path.sep}package.json`);
    const curVersion = JSON.parse(pkgData).version;
    const prevFilePath = `${extPath}${path.sep}version`;
    let prevVersion;
    if (await exists(prevFilePath)) {
        prevVersion = await readFile(prevFilePath);
    }
    if (getMajorMinor(curVersion) === getMajorMinor(prevVersion)) {
        return;
    }
    await writeFile(prevFilePath, curVersion);
    const showOpt = 'Show changelog';
    const dismissOpt = 'Dismiss';
    const opt = await vscode.window.showInformationMessage('TLA+ extension has been updated.', showOpt, dismissOpt);
    if (opt === showOpt) {
        vscode.commands.executeCommand('vscode.open', CHANGELOG_URL);
    }
}

function getMajorMinor(version: string | undefined): string | undefined {
    if (!version || version === '') {
        return undefined;
    }
    const matches = /^(\d+.\d+)/g.exec(version);
    return matches ? matches[1] : undefined;
}
