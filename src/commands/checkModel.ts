import * as vscode from 'vscode';
import * as path from 'path';
import { exists, copyFile, readdir } from 'fs';
import { runTlc, stopProcess } from '../tla2tools';
import { TlcModelCheckerStdoutParser } from '../parsers/tlc';
import { updateCheckResultView, revealEmptyCheckResultView, revealLastCheckResultView } from '../checkResultView';
import { applyDCollection } from '../diagnostic';
import { ChildProcess } from 'child_process';
import { saveStreamToFile } from '../outputSaver';
import { replaceExtension } from '../common';
import { ModelCheckResultSource } from '../model/check';
import { ToolOutputChannel } from '../outputChannels';

export const CMD_CHECK_MODEL_RUN = 'tlaplus.model.check.run';
export const CMD_CHECK_MODEL_CUSTOM_RUN = 'tlaplus.model.check.customRun';
export const CMD_CHECK_MODEL_STOP = 'tlaplus.model.check.stop';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';
export const CMD_SHOW_TLC_OUTPUT = 'tlaplus.showTlcOutput';

const CFG_CREATE_OUT_FILES = 'tlaplus.tlc.modelChecker.createOutFiles';
const TEMPLATE_CFG_PATH = path.resolve(__dirname, '../../../tools/template.cfg');

let checkProcess: ChildProcess | undefined;
const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);
const outChannel = new ToolOutputChannel('TLC', mapTlcOutputLine);

class SpecFiles {
    constructor(
        readonly tlaFilePath: string,
        readonly cfgFilePath: string
    ) {}
}

/**
 * Runs TLC on a TLA+ specification.
 */
export async function checkModel(diagnostic: vscode.DiagnosticCollection, extContext: vscode.ExtensionContext) {
    const doc = getDocumentIfCanRun(extContext);
    if (!doc) {
        return;
    }
    if (doc.languageId !== 'tlaplus' && doc.languageId !== 'tlaplus.cfg') {
        vscode.window.showWarningMessage(
            'File in the active editor is not a .tla or .cfg file, it cannot be checked as a model');
        return;
    }
    const specFiles = await getSpecFiles(doc.uri);
    if (!specFiles) {
        return;
    }
    doCheckModel(specFiles, extContext, diagnostic);
}

export async function checkModelCustom(diagnostic: vscode.DiagnosticCollection, extContext: vscode.ExtensionContext) {
    const doc = getDocumentIfCanRun(extContext);
    if (!doc) {
        return;
    }
    if (doc.languageId !== 'tlaplus') {
        vscode.window.showWarningMessage('File in the active editor is not a .tla, it cannot be checked as a model');
        return;
    }
    const cfgFileName = await vscode.window.showQuickPick(
        findConfigFiles(path.dirname(doc.uri.fsPath)),
        { canPickMany: false, placeHolder: 'Select a model config file', matchOnDetail: true }
    );
    if (!cfgFileName || cfgFileName.length === 0) {
        return;
    }
    const specFiles = new SpecFiles(
        doc.uri.fsPath,
        path.join(path.dirname(doc.uri.fsPath), cfgFileName)
    );
    doCheckModel(specFiles, extContext, diagnostic);
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

async function doCheckModel(
    specFiles: SpecFiles,
    extContext: vscode.ExtensionContext,
    diagnostic: vscode.DiagnosticCollection
) {
    try {
        updateStatusBarItem(true);
        const procInfo = await runTlc(specFiles.tlaFilePath, path.basename(specFiles.cfgFilePath));
        outChannel.bindTo(procInfo);
        checkProcess = procInfo.process;
        checkProcess.on('close', () => {
            checkProcess = undefined;
            updateStatusBarItem(false);
        });
        attachFileSaver(specFiles.tlaFilePath, checkProcess);
        revealEmptyCheckResultView(ModelCheckResultSource.Process, extContext);
        const stdoutParser = new TlcModelCheckerStdoutParser(
            ModelCheckResultSource.Process,
            checkProcess.stdout,
            specFiles.tlaFilePath,
            true,
            updateCheckResultView);
        const dCol = await stdoutParser.readAll();
        applyDCollection(dCol, diagnostic);
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
    return new Promise(resolve => {
        exists(modulePath, (exists) => {
            if (!exists) {
                const moduleFile = path.basename(modulePath);
                vscode.window.showWarningMessage(`Corresponding TLA+ module file ${moduleFile} doesn't exist.`);
            }
            resolve(exists);
        });
    });
}

async function checkModelExists(cfgPath: string): Promise<boolean> {
    return new Promise(resolve => {
        exists(cfgPath, (exists) => {
            if (!exists) {
                showConfigAbsenceWarning(cfgPath);
            }
            resolve(exists);
        });
    });
}

function updateStatusBarItem(active: boolean) {
    statusBarItem.text = 'TLC' + (active ? ' $(gear~spin)' : '');
    statusBarItem.tooltip = 'TLA+ model checking' + (active ? ' is running' : ' result');
    statusBarItem.command = CMD_CHECK_MODEL_DISPLAY;
    statusBarItem.show();
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

/**
 * Returns the list of .cfg-files in the given directory.
 */
async function findConfigFiles(path: string): Promise<string[]> {
    return new Promise<string[]>((resolve, reject) => {
        readdir(path, (err, files) => {
            if (err) {
                reject(err);
                return;
            }
            const configs = files.filter(f => f.endsWith('.cfg'));
            resolve(configs.sort());
        });
    });
}

function getDocumentIfCanRun(extContext: vscode.ExtensionContext): vscode.TextDocument | undefined {
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
    return editor.document;
}
