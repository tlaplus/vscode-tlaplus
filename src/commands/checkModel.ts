import * as vscode from 'vscode';
import * as path from 'path';
import { copyFile } from 'fs';
import { runTlc, stopProcess } from '../tla2tools';
import { TlcModelCheckerStdoutParser } from '../parsers/tlc';
import { updateCheckResultView, revealEmptyCheckResultView, revealLastCheckResultView } from '../checkResultView';
import { applyDCollection } from '../diagnostic';
import { ChildProcess } from 'child_process';
import { saveStreamToFile } from '../outputSaver';
import { replaceExtension, LANG_TLAPLUS, LANG_TLAPLUS_CFG, listFiles, exists } from '../common';
import { ModelCheckResultSource, ModelCheckResult } from '../model/check';
import { ToolOutputChannel } from '../outputChannels';

export const CMD_CHECK_MODEL_RUN = 'tlaplus.model.check.run';
export const CMD_CHECK_MODEL_REPEAT = 'tlaplus.model.check.repeat';
export const CMD_CHECK_MODEL_CUSTOM_RUN = 'tlaplus.model.check.customRun';
export const CMD_CHECK_MODEL_STOP = 'tlaplus.model.check.stop';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';
export const CMD_SHOW_TLC_OUTPUT = 'tlaplus.showTlcOutput';
export const CTX_TLC_RUNNING = 'tlaplus.tlc.isRunning';
export const CTX_TLC_CAN_REPEAT = 'tlaplus.tlc.canRepeat';

const CFG_CREATE_OUT_FILES = 'tlaplus.tlc.modelChecker.createOutFiles';
const TEMPLATE_CFG_PATH = path.resolve(__dirname, '../../../tools/template.cfg');

let checkProcess: ChildProcess | undefined;
let lastCheckFiles: SpecFiles | undefined;
const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);
const outChannel = new ToolOutputChannel('TLC', mapTlcOutputLine);

class CheckResultHolder {
    checkResult: ModelCheckResult | undefined;
}

export class SpecFiles {
    constructor(
        readonly tlaFilePath: string,
        readonly cfgFilePath: string
    ) {}
}

/**
 * Runs TLC on a TLA+ specification.
 */
export async function checkModel(
    fileUri: vscode.Uri | undefined,
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
) {
    const uri = fileUri ? fileUri : getActiveEditorFileUri(extContext);
    if (!uri) {
        return;
    }
    const specFiles = await getSpecFiles(uri);
    if (!specFiles) {
        return;
    }
    doCheckModel(specFiles, false, extContext, diagnostic);
}

export async function repeatLastCheck(
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
) {
    if (!lastCheckFiles) {
        vscode.window.showWarningMessage('No check to repeat');
        return;
    }
    doCheckModel(lastCheckFiles, false, extContext, diagnostic);
}

export async function checkModelCustom(diagnostic: vscode.DiagnosticCollection, extContext: vscode.ExtensionContext) {
    const editor = getEditorIfCanRunTlc(extContext);
    if (!editor) {
        return;
    }
    const doc = editor.document;
    if (doc.languageId !== LANG_TLAPLUS) {
        vscode.window.showWarningMessage('File in the active editor is not a .tla, it cannot be checked as a model');
        return;
    }
    const configFiles = await listFiles(path.dirname(doc.uri.fsPath), (fName) => fName.endsWith('.cfg'));
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
    doCheckModel(specFiles, false, extContext, diagnostic);
}

/**
 * Reveals model checking view panel.
 */
export function displayModelChecking(extContext: vscode.ExtensionContext) {
    revealLastCheckResultView(extContext);
}

/**
 * Stops the current model checking process.
 */
export function stopModelChecking() {
    if (checkProcess) {
        stopProcess(checkProcess);
    } else {
        vscode.window.showInformationMessage("There're no currently running model checking processes");
    }
}

export function showTlcOutput() {
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
    if (checkProcess) {
        vscode.window.showWarningMessage(
                'Another model checking process is currently running',
                'Show currently running process'
            ).then(() => revealLastCheckResultView(extContext));
        return undefined;
    }
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ model to check');
        return undefined;
    }
    return editor;
}

export async function doCheckModel(
    specFiles: SpecFiles,
    quiet: boolean,
    extContext: vscode.ExtensionContext,
    diagnostic: vscode.DiagnosticCollection
): Promise<ModelCheckResult | undefined> {
    try {
        lastCheckFiles = specFiles;
        vscode.commands.executeCommand('setContext', CTX_TLC_CAN_REPEAT, true);
        updateStatusBarItem(true);
        const procInfo = await runTlc(specFiles.tlaFilePath, path.basename(specFiles.cfgFilePath));
        outChannel.bindTo(procInfo);
        checkProcess = procInfo.process;
        checkProcess.on('close', () => {
            checkProcess = undefined;
            updateStatusBarItem(false);
        });
        if (!quiet) {
            attachFileSaver(specFiles.tlaFilePath, checkProcess);
            revealEmptyCheckResultView(ModelCheckResultSource.Process, extContext);
        }
        const resultHolder = new CheckResultHolder();
        const stdoutParser = new TlcModelCheckerStdoutParser(
            ModelCheckResultSource.Process,
            checkProcess.stdout,
            specFiles.tlaFilePath,
            true,
            (checkResult) => {
                resultHolder.checkResult = checkResult;
                if (!quiet) {
                    updateCheckResultView(checkResult);
                }
            });
        const dCol = await stdoutParser.readAll();
        if (!quiet) {
            applyDCollection(dCol, diagnostic);
        }
        return resultHolder.checkResult;
    } catch (err) {
        statusBarItem.hide();
        vscode.window.showErrorMessage(err.message);
    }
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
async function getSpecFiles(fileUri: vscode.Uri): Promise<SpecFiles | undefined> {
    const filePath = fileUri.fsPath;
    let specFiles;
    let canRun = true;
    if (filePath.endsWith('.cfg')) {
        specFiles = new SpecFiles(replaceExtension(filePath, 'tla'), filePath);
        canRun = await checkModuleExists(specFiles.tlaFilePath);
    } else if (filePath.endsWith('.tla')) {
        specFiles = new SpecFiles(filePath, replaceExtension(filePath, 'cfg'));
        canRun = await checkModelExists(specFiles.cfgFilePath);
    }
    return canRun ? specFiles : undefined;
}

async function checkModuleExists(modulePath: string): Promise<boolean> {
    const moduleExists = await exists(modulePath);
    if (!moduleExists) {
        const moduleFile = path.basename(modulePath);
        vscode.window.showWarningMessage(`Corresponding TLA+ module file ${moduleFile} doesn't exist.`);
    }
    return moduleExists;
}

async function checkModelExists(cfgPath: string): Promise<boolean> {
    const cfgExists = await exists(cfgPath);
    if (!cfgExists) {
        showConfigAbsenceWarning(cfgPath);
    }
    return cfgExists;
}

function updateStatusBarItem(active: boolean) {
    statusBarItem.text = 'TLC' + (active ? ' $(gear~spin)' : '');
    statusBarItem.tooltip = 'TLA+ model checking' + (active ? ' is running' : ' result');
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

function mapTlcOutputLine(line: string): string | undefined {
    if (line === '') {
        return line;
    }
    const cleanLine = line.replace(/@!@!@(START|END)MSG \d+(\:\d+)? @!@!@/g, '');
    return cleanLine === '' ? undefined : cleanLine;
}
