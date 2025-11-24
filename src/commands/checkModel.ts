import { ChildProcess } from 'child_process';
import { copyFile } from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { Utils } from 'vscode-uri';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG, exists, listFiles, replaceExtension } from '../common';
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
import { TlcCoverageDecorationProvider } from '../tlcCoverage';

export const CMD_CHECK_MODEL_RUN = 'tlaplus.model.check.run';
export const CMD_CHECK_MODEL_RUN_AGAIN = 'tlaplus.model.check.runAgain';
export const CMD_CHECK_MODEL_CUSTOM_RUN = 'tlaplus.model.check.customRun';
export const CMD_CHECK_MODEL_STOP = 'tlaplus.model.check.stop';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';
export const CMD_SHOW_TLC_OUTPUT = 'tlaplus.showTlcOutput';
export const CTX_TLC_RUNNING = 'tlaplus.tlc.isRunning';
export const CTX_TLC_CAN_RUN_AGAIN = 'tlaplus.tlc.canRunAgain';

const CFG_CREATE_OUT_FILES = 'tlaplus.tlc.modelChecker.createOutFiles';
const TEMPLATE_CFG_PATH = path.resolve(__dirname, '../tools/template.cfg');

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
    if (doc.languageId !== LANG_TLAPLUS) {
        vscode.window.showWarningMessage('File in the active editor is not a .tla, it cannot be checked as a model');
        return;
    }
    // Accept .tla files here because TLC configs and TLA+ modules can share the same file:
    // https://github.com/tlaplus/vscode-tlaplus/issues/220
    const configFiles = await listFiles(path.dirname(doc.uri.fsPath),
        (fName) => fName.endsWith('.cfg') || fName.endsWith('.tla'));
    configFiles.sort();
    const cfgFileName = await vscode.window.showQuickPick(
        configFiles,
        { canPickMany: false, placeHolder: 'Select a model config file', matchOnDetail: true }
    );
    if (!cfgFileName || cfgFileName.length === 0) {
        return;
    }
    const specFiles = new SpecFiles(
        doc.uri.fsPath,
        path.join(path.dirname(doc.uri.fsPath), cfgFileName)
    );
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
            specFiles.tlaFilePath, path.basename(specFiles.cfgFilePath), showOptionsPrompt, extraOpts);
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
            attachFileSaver(specFiles.tlaFilePath, checkProcess);
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
        return resultHolder.checkResult;
    } catch (err) {
        statusBarItem.hide();
        vscode.window.showErrorMessage(`Error checking model: ${err}`);
    }
    return undefined;
}

function attachFileSaver(tlaFilePath: string, proc: ChildProcess) {
    const createOutFiles = vscode.workspace.getConfiguration().get<boolean>(CFG_CREATE_OUT_FILES);
    if (typeof(createOutFiles) === 'undefined' || createOutFiles) {
        const outFilePath = replaceExtension(tlaFilePath, 'out');
        saveStreamToFile(proc.stdout, outFilePath);
    }
}

/**
 * Finds all files that needed to run model check.
 */
export async function getSpecFiles(fileUri: vscode.Uri, warn = true, prefix = 'MC'): Promise<SpecFiles | undefined> {
    let specFiles;

    // a) Check the given input if it exists.
    specFiles = await checkSpecFiles(fileUri, false);
    if (specFiles) {
        return specFiles;
    }
    // b) Check alternatives:
    // Unless the given filePath already starts with 'MC', prepend MC to the name
    // and check if it exists. If yes, it becomes the spec file.  If not, fall back
    // to the original file.  The assumptions is that a user usually has  Spec.tla
    // open in the editor and doesn't want to switch to  MC.tla  before model-checking.
    // TODO: Ideally, we wouldn't just check filenames here but check the parse result
    // TODO: if the module in  MCSpec.tla  actually extends the module in  Spec.
    const b = Utils.basename(fileUri);
    if (!b.startsWith(prefix) && !b.endsWith('.cfg')) {
        const str = fileUri.toString();
        const n = str.substr(0, str.lastIndexOf(b)) + prefix + b;
        const filePath = vscode.Uri.parse(n).fsPath;
        specFiles = new SpecFiles(filePath, replaceExtension(filePath, 'cfg'));
        // Here, we make sure that the .cfg *and* the .tla exist.
        let canRun = true;
        canRun = await checkModelExists(specFiles.cfgFilePath, warn);
        canRun = canRun && await checkModuleExists(specFiles.tlaFilePath, warn);
        if (canRun) {
            return specFiles;
        }
    }
    // c) Deliberately trigger the warning dialog by checking the given input again
    // knowing that it doesn't exist.
    return await checkSpecFiles(fileUri, warn);
}

async function checkSpecFiles(fileUri: vscode.Uri, warn = true): Promise<SpecFiles | undefined> {
    const filePath = fileUri.fsPath;
    let specFiles;
    let canRun = true;
    if (filePath.endsWith('.cfg')) {
        specFiles = new SpecFiles(replaceExtension(filePath, 'tla'), filePath);
        canRun = await checkModuleExists(specFiles.tlaFilePath, warn);
    } else if (filePath.endsWith('.tla')) {
        specFiles = new SpecFiles(filePath, replaceExtension(filePath, 'cfg'));
        canRun = await checkModelExists(specFiles.cfgFilePath, warn);
    }
    return canRun ? specFiles : undefined;
}

async function checkModuleExists(modulePath: string, warn = true): Promise<boolean> {
    const moduleExists = await exists(modulePath);
    if (!moduleExists && warn) {
        const moduleFile = path.basename(modulePath);
        vscode.window.showWarningMessage(`Corresponding TLA+ module file ${moduleFile} doesn't exist.`);
    }
    return moduleExists;
}

async function checkModelExists(cfgPath: string, warn = true): Promise<boolean> {
    const cfgExists = await exists(cfgPath);
    if (!cfgExists && warn) {
        showConfigAbsenceWarning(cfgPath);
    }
    return cfgExists;
}

function updateStatusBarItem(active: boolean, specFiles: SpecFiles | undefined) {
    statusBarItem.text = 'TLC' + (active ?
        (specFiles === undefined ? '' : ' (' + specFiles.tlaFileName + '/' + specFiles.cfgFileName + ')')
        + ' $(gear~spin)' : '');
    statusBarItem.tooltip = 'TLA+ model checking' + (active ?
        (specFiles === undefined ? '' : ' of ' + specFiles.tlaFileName + '/' + specFiles.cfgFileName)
        + ' is running' : ' result');
    statusBarItem.command = CMD_CHECK_MODEL_DISPLAY;
    statusBarItem.show();
    vscode.commands.executeCommand('setContext', CTX_TLC_RUNNING, active);
}

function showConfigAbsenceWarning(cfgPath: string) {
    const fileName = path.basename(cfgPath);
    const createOption = 'Create model file';
    vscode.window.showWarningMessage(`Model file ${fileName} doesn't exist. Cannot check model.`, createOption)
        .then((option) => {
            if (option === createOption) {
                createModelFile(cfgPath);
            }
        });
}

async function createModelFile(cfgPath: string) {
    copyFile(TEMPLATE_CFG_PATH, cfgPath, (err) => {
        if (err) {
            console.warn(`Error creating config file: ${err}`);
            vscode.window.showWarningMessage(`Cannot create model file: ${err}`);
            return;
        }
        vscode.workspace.openTextDocument(cfgPath)
            .then(doc => vscode.window.showTextDocument(doc));
    });
}

export function mapTlcOutputLine(line: string): string | undefined {
    if (line === '') {
        return line;
    }
    const cleanLine = line.replace(/@!@!@(START|END)MSG \d+(:\d+)? @!@!@/g, '');
    return cleanLine === '' ? undefined : cleanLine;
}
