import { ChildProcess } from 'child_process';
import * as path from 'path';
import * as vscode from 'vscode';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG } from '../common';
import { applyDCollection } from '../diagnostic';
import { ModelCheckResult, ModelCheckResultSource, SpecFiles } from '../model/check';
import { ToolOutputChannel } from '../outputChannels';
import { saveStreamToFile } from '../outputSaver';
import {
    revealEmptyCheckResultView,
    revealLastCheckResultView,
    updateCheckResultView
} from '../panels/checkResultView';
import { TlcModelCheckerStdoutParser } from '../parsers/tlc';
import { runTlc, stopProcess } from '../tla2tools';
import { ModelResolveMode, resolveModelForUri } from './modelResolver';
import { TlcCoverageDecorationProvider } from '../tlcCoverage';
import { tlcTraceToPuml } from '../generators/tlcTraceToPuml';
import { showSequenceDiagramFromPuml } from '../panels/sequenceDiagramView';

export const CMD_CHECK_MODEL_RUN = 'tlaplus.model.check.run';
export const CMD_CHECK_MODEL_RUN_AGAIN = 'tlaplus.model.check.runAgain';
export const CMD_CHECK_MODEL_CUSTOM_RUN = 'tlaplus.model.check.customRun';
export const CMD_CHECK_MODEL_STOP = 'tlaplus.model.check.stop';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';
export const CMD_SHOW_TLC_OUTPUT = 'tlaplus.showTlcOutput';
export const CTX_TLC_RUNNING = 'tlaplus.tlc.isRunning';
export const CTX_TLC_CAN_RUN_AGAIN = 'tlaplus.tlc.canRunAgain';

const CFG_CREATE_OUT_FILES = 'tlaplus.tlc.modelChecker.createOutFiles';
const CFG_SEQ_DIAGRAM_TRACE_VAR = 'tlaplus.tlc.sequenceDiagram.traceVariable';
let checkProcess: ChildProcess | undefined;
let lastCheckFiles: SpecFiles | undefined;
let coverageProvider: TlcCoverageDecorationProvider | undefined;
const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);
export const outChannel = new ToolOutputChannel('TLC', mapTlcOutputLine);

class CheckResultHolder {
    checkResult: ModelCheckResult | undefined;
}

/**
 * Sets the coverage provider to be used for visualization.
 */
export function setCoverageProvider(provider: TlcCoverageDecorationProvider): void {
    coverageProvider = provider;
}

/**
 * Runs TLC on a TLA+ specification.
 */
export async function checkModel(
    fileUri: vscode.Uri | undefined,
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
): Promise<void> {
    const uri = fileUri ? fileUri : getActiveEditorFileUri(extContext);
    if (!uri) {
        return;
    }

    const specFiles = await getSpecFiles(uri, true);
    if (!specFiles) {
        return;
    }
    await doCheckModel(specFiles, true, extContext, diagnostic, true);
}

export async function runLastCheckAgain(
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
): Promise<void> {
    if (!lastCheckFiles) {
        vscode.window.showWarningMessage('No last check to run');
        return;
    }
    if (!canRunTlc(extContext)) {
        return;
    }
    await doCheckModel(lastCheckFiles, true, extContext, diagnostic, false);
}

export async function checkModelCustom(
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
): Promise<void> {
    const editor = getEditorIfCanRunTlc(extContext);
    if (!editor) {
        return;
    }
    const doc = editor.document;
    if (doc.languageId !== LANG_TLAPLUS && doc.languageId !== LANG_TLAPLUS_CFG) {
        vscode.window.showWarningMessage(
            'File in the active editor is not a .tla or .cfg, it cannot be checked as a model');
        return;
    }
    const specFiles = await getSpecFiles(doc.uri, true, true, 'customPick');
    if (!specFiles) {
        return;
    }
    await doCheckModel(specFiles, true, extContext, diagnostic, true);
}

/**
 * Reveals model checking view panel.
 */
export function displayModelChecking(extContext: vscode.ExtensionContext): void {
    revealLastCheckResultView(extContext);
}

/**
 * Stops the current model checking process.
 */
export function stopModelChecking(
    terminateLastRun: (lastSpecFiles: SpecFiles | undefined) => boolean =
    (): boolean => { return true; },
    silent: boolean = false
): void {
    if (checkProcess && terminateLastRun(lastCheckFiles)) {
        stopProcess(checkProcess);
    } else if (!silent) {
        vscode.window.showInformationMessage("There're no currently running model checking processes");
    }
}

export function showTlcOutput(): void {
    outChannel.revealWindow();
}

function getActiveEditorFileUri(extContext: vscode.ExtensionContext): vscode.Uri | undefined {
    const editor = getEditorIfCanRunTlc(extContext);
    if (!editor) {
        return undefined;
    }
    const doc = editor.document;
    if (doc.languageId !== LANG_TLAPLUS && doc.languageId !== LANG_TLAPLUS_CFG) {
        vscode.window.showWarningMessage(
            'File in the active editor is not a .tla or .cfg file, it cannot be checked as a model');
        return undefined;
    }
    return doc.uri;
}

export function getEditorIfCanRunTlc(extContext: vscode.ExtensionContext): vscode.TextEditor | undefined {
    if (!canRunTlc(extContext)) {
        return undefined;
    }
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ model to check');
        return undefined;
    }
    return editor;
}

function canRunTlc(extContext: vscode.ExtensionContext): boolean {
    if (checkProcess) {
        vscode.window.showWarningMessage(
            'Another model checking process is currently running',
            'Show currently running process'
        ).then(() => revealLastCheckResultView(extContext));
        return false;
    }
    return true;
}

export async function doCheckModel(
    specFiles: SpecFiles,
    showCheckResultView: boolean,
    extContext: vscode.ExtensionContext,
    diagnostic: vscode.DiagnosticCollection,
    showOptionsPrompt: boolean,
    extraOpts: string[] = [],
    debuggerPortCallback?: (port?: number) => void
): Promise<ModelCheckResult | undefined> {
    try {
        const procInfo = await runTlc(
            specFiles.tlaFilePath, specFiles.cfgFilePath, showOptionsPrompt, extraOpts);
        if (procInfo === undefined) {
            // Command cancelled by user, make sure UI state is reset
            vscode.commands.executeCommand('setContext', CTX_TLC_CAN_RUN_AGAIN, !!lastCheckFiles);
            updateStatusBarItem(false, lastCheckFiles);
            return undefined;
        }
        lastCheckFiles = specFiles;
        vscode.commands.executeCommand('setContext', CTX_TLC_CAN_RUN_AGAIN, true);
        updateStatusBarItem(true, specFiles);
        outChannel.bindTo(procInfo);
        checkProcess = procInfo.process;
        checkProcess.on('close', () => {
            checkProcess = undefined;
            updateStatusBarItem(false, lastCheckFiles);
        });
        if (showCheckResultView) {
            attachFileSaver(specFiles, checkProcess);
            revealEmptyCheckResultView(extContext);
        }
        const resultHolder = new CheckResultHolder();
        const checkResultCallback = (checkResult: ModelCheckResult) => {
            resultHolder.checkResult = checkResult;
            if (showCheckResultView) {
                updateCheckResultView(checkResult);
            }

            // Update coverage visualization
            if (coverageProvider && checkResult.coverageStat.length > 0) {
                // Get total distinct states from the last entry in initialStatesStat
                let totalDistinctStates = 0;
                if (checkResult.initialStatesStat.length > 0) {
                    const lastStat = checkResult.initialStatesStat[checkResult.initialStatesStat.length - 1];
                    totalDistinctStates = lastStat.distinct;
                }
                coverageProvider.updateCoverage(checkResult.coverageStat, totalDistinctStates);
            }
        };
        // Accumulate raw stdout for sequence-diagram generation
        const rawChunks: string[] = [];
        if (checkProcess.stdout) {
            checkProcess.stdout.on('data', (chunk: Buffer | string) => {
                rawChunks.push(String(chunk));
            });
        }
        const stdoutParser = new TlcModelCheckerStdoutParser(
            ModelCheckResultSource.Process,
            checkProcess.stdout,
            specFiles,
            true,
            checkResultCallback,
            debuggerPortCallback
        );
        const dCol = await stdoutParser.readAll();
        applyDCollection(dCol, diagnostic);
        // Auto-generate PlantUML sequence diagram from TLC error trace
        tryGenerateSequenceDiagram(rawChunks.join(''), specFiles, extContext);
        return resultHolder.checkResult;
    } catch (err) {
        statusBarItem.hide();
        vscode.window.showErrorMessage(`Error checking model: ${err}`);
    }
    return undefined;
}

function attachFileSaver(specFiles: SpecFiles, proc: ChildProcess) {
    const createOutFiles = vscode.workspace.getConfiguration().get<boolean>(CFG_CREATE_OUT_FILES);
    if (typeof(createOutFiles) === 'undefined' || createOutFiles) {
        const outFilePath = path.join(specFiles.outputDir, `${specFiles.modelName}.out`);
        saveStreamToFile(proc.stdout, outFilePath);
    }
}

/**
 * Finds all files that needed to run model check.
 */
export async function getSpecFiles(
    fileUri: vscode.Uri,
    warn = true,
    interactive = true,
    mode: ModelResolveMode = 'adjacent'
): Promise<SpecFiles | undefined> {
    const resolved = await resolveModelForUri(fileUri, warn, interactive, mode);
    if (!resolved) {
        return undefined;
    }
    return new SpecFiles(
        resolved.tlaPath,
        resolved.cfgPath,
        resolved.modelName,
        resolved.outputDir
    );
}

function updateStatusBarItem(active: boolean, specFiles: SpecFiles | undefined) {
    statusBarItem.text = 'TLC' + (active ?
        (specFiles === undefined ? '' : ` (Model: ${specFiles.modelName})`)
        + ' $(gear~spin)' : '');
    statusBarItem.tooltip = 'TLA+ model checking' + (active ?
        (specFiles === undefined ? '' : ` of model ${specFiles.modelName}`)
        + ' is running' : ' result');
    statusBarItem.command = CMD_CHECK_MODEL_DISPLAY;
    statusBarItem.show();
    vscode.commands.executeCommand('setContext', CTX_TLC_RUNNING, active);
}


export function mapTlcOutputLine(line: string): string | undefined {
    if (line === '') {
        return line;
    }
    const cleanLine = line.replace(/@!@!@(START|END)MSG \d+(:\d+)? @!@!@/g, '');
    return cleanLine === '' ? undefined : cleanLine;
}

/**
 * Attempts to generate a PlantUML sequence diagram from raw TLC output.
 * Errors are logged to the TLC output channel, never thrown.
 */
function tryGenerateSequenceDiagram(
    rawOutput: string,
    specFiles: SpecFiles,
    extContext: vscode.ExtensionContext,
): void {
    try {
        const traceVar = vscode.workspace.getConfiguration()
            .get<string>(CFG_SEQ_DIAGRAM_TRACE_VAR) ?? '_seqDiagramTrace';
        const puml = tlcTraceToPuml(rawOutput, {
            traceVariable: traceVar,
            title: specFiles.modelName,
        });
        if (puml) {
            showSequenceDiagramFromPuml(puml, extContext, specFiles.modelName)
                .catch(err => {
                    outChannel.appendLine(`[Sequence Diagram] Failed to open editor: ${err}`);
                });
        }
    } catch (err) {
        outChannel.appendLine(`[Sequence Diagram] Failed to generate: ${err}`);
    }
}
