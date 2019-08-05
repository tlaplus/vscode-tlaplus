import * as vscode from 'vscode';
import * as path from 'path';
import { exists, copyFile } from 'fs';
import { runTool, stopProcess } from '../tla2tools';
import { TLCModelCheckerStdoutParser } from '../parsers/tlc';
import { revealCheckResultView, updateCheckResultView, revealEmptyCheckResultView } from '../checkResultView';
import { applyDCollection } from '../diagnostic';
import { ChildProcess } from 'child_process';

export const CMD_CHECK_MODEL_RUN = 'tlaplus.model.check.run';
export const CMD_CHECK_MODEL_STOP = 'tlaplus.model.check.stop';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';

const TEMPLATE_CFG_PATH = path.resolve(__dirname, '../../tools/template.cfg');

let checkProcess: ChildProcess | undefined;
const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);

class SpecFiles {
    constructor(
        readonly tlaFilePath: string,
        readonly cfgFilePath: string
    ) {}
}

/**
 * Runs TLC on a TLA+ specification.
 */
export function checkModel(diagnostic: vscode.DiagnosticCollection, extContext: vscode.ExtensionContext) {
    if (checkProcess) {
        vscode.window.showWarningMessage(
                'Another model checking process is currently running',
                'Show currently running process'
            ).then(() => revealCheckResultView(extContext));
        return;
    }
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ model to check');
        return;
    }
    if (editor.document.languageId !== 'tlaplus' && editor.document.languageId !== 'cfg') {
        vscode.window.showWarningMessage(
            'File in the active editor is not a .tla or .cfg file, it cannot be checked as a model');
        return;
    }
    doCheckModel(editor.document.uri, extContext, diagnostic);
}

/**
 * Reveals model checking view panel.
 */
export function displayModelChecking(extContext: vscode.ExtensionContext) {
    revealCheckResultView(extContext);
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

async function doCheckModel(
    fileUri: vscode.Uri,
    extContext: vscode.ExtensionContext,
    diagnostic: vscode.DiagnosticCollection
) {
    const specFiles = await getSpecFiles(fileUri);
    if (!specFiles) {
        return;
    }
    try {
        updateStatusBarItem(true);
        checkProcess = await runTool(
            'tlc2.TLC',
            specFiles.tlaFilePath,
            ['-modelcheck', '-coverage', '1', '-tool', '-config', path.basename(specFiles.cfgFilePath)]);
        checkProcess.on('close', () => {
            checkProcess = undefined;
            updateStatusBarItem(false);
        });
        revealEmptyCheckResultView(extContext);
        const stdoutParser = new TLCModelCheckerStdoutParser(
            checkProcess.stdout, specFiles.tlaFilePath, updateCheckResultView);
        const dCol = await stdoutParser.readAll();
        applyDCollection(dCol, diagnostic);
    } catch (err) {
        statusBarItem.hide();
        vscode.window.showErrorMessage(err.message);
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
    return new Promise((resolve) => {
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
    return new Promise((resolve) => {
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

function replaceExtension(filePath: string, newExt: string): string {
    const lastDotIdx = filePath.lastIndexOf('.');
    const basePath = lastDotIdx < 0 ? filePath : filePath.substring(0, lastDotIdx);
    return basePath + '.' + newExt;
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
