import * as vscode from 'vscode';
import * as path from 'path';
import { copyFile } from 'fs';
import { runTlc, stopProcess } from '../tla2tools';
import { TlcModelCheckerStdoutParser } from '../parsers/tlc';
import { updateCheckResultView, revealEmptyCheckResultView, revealLastCheckResultView } from '../checkResultView';
import { applyDCollection } from '../diagnostic';
import { ChildProcess } from 'child_process';
import { saveStreamToFile } from '../outputSaver';
import { replaceExtension, LANG_TLAPLUS, LANG_TLAPLUS_CFG, listFiles, exists, ModelCheckingError } from '../common';
import { ModelCheckResultSource, ModelCheckResult, SpecFiles } from '../model/check';
import { ToolOutputChannel } from '../outputChannels';
import { Utils } from 'vscode-uri';
import { Result, ok, err } from 'neverthrow';

export const CMD_CHECK_MODEL_RUN = 'tlaplus.model.check.run';
export const CMD_CHECK_MODEL_RUN_AGAIN = 'tlaplus.model.check.runAgain';
export const CMD_CHECK_MODEL_CUSTOM_RUN = 'tlaplus.model.check.customRun';
export const CMD_CHECK_MODEL_STOP = 'tlaplus.model.check.stop';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';
export const CMD_SHOW_TLC_OUTPUT = 'tlaplus.showTlcOutput';
export const CTX_TLC_RUNNING = 'tlaplus.tlc.isRunning';
export const CTX_TLC_CAN_RUN_AGAIN = 'tlaplus.tlc.canRunAgain';

const CFG_CREATE_OUT_FILES = 'tlaplus.tlc.modelChecker.createOutFiles';
const TEMPLATE_CFG_PATH = path.resolve(__dirname, '../../../tools/template.cfg');

let checkProcess: ChildProcess | undefined;
let lastCheckFiles: SpecFiles | undefined;
const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);
const outChannel = new ToolOutputChannel('TLC', mapTlcOutputLine);

class CheckResultHolder {
    checkResult: ModelCheckResult | undefined;
}

/**
 * Runs TLC on a TLA+ specification.
 */
export async function checkModel(
    fileUri: vscode.Uri | undefined,
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
): Promise<void> {
    // We need to check canRunTlc separately from getActiveEditorFileUri() since checkModel could silently drop an
    // error related to canRunTlc when checking using the previous spec.
    if (!canRunTlc(extContext)) {
        return;
    }

    const uriResult = fileUri ? ok(fileUri) : getActiveEditorFileUri(extContext);

    const specFilesResult = await uriResult.match(
        async (uri: vscode.Uri): Promise<Result<SpecFiles, ModelCheckingError>> => {
            const files = await getSpecFiles(uri, false);
            if (!files) {
                return err(new ModelCheckingError('Could not load spec files.'));
            }
            return ok(files);
        },
        // Use last checked spec if no active TLA+ files are found.
        async (error: unknown): Promise<Result<SpecFiles, ModelCheckingError>> => lastCheckFiles ?
            ok(lastCheckFiles) :
            err(new ModelCheckingError(
                'No active TLA+ file or previous spec found. Switch to the .tla or .cfg file to check.'
            ))
    );

    if (specFilesResult.isErr()) {
        vscode.window.showErrorMessage(specFilesResult.error.message);
        return;
    }

    doCheckModel(specFilesResult.value, true, extContext, diagnostic, true);
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
    doCheckModel(lastCheckFiles, true, extContext, diagnostic, false);
}

export async function checkModelCustom(
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
): Promise<void> {
    const editorResult = getEditorIfCanRunTlc(extContext);
    if (editorResult.isErr()) {
        vscode.window.showErrorMessage(editorResult.error.message);
        return;
    }
    const doc = editorResult.value.document;
    if (doc.languageId !== LANG_TLAPLUS) {
        vscode.window.showWarningMessage('File in the active editor is not a .tla, it cannot be checked as a model');
        return;
    }
    // Accept .tla files here because TLC configs and TLA+ modules can share the same file:
    // https://github.com/alygin/vscode-tlaplus/issues/220
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
    doCheckModel(specFiles, true, extContext, diagnostic, true);
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
    (lastSpecFiles: SpecFiles | undefined): boolean => { return true; },
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

function getActiveEditorFileUri(extContext: vscode.ExtensionContext): Result<vscode.Uri, ModelCheckingError> {
    const editorResult = getEditorIfCanRunTlc(extContext);

    if (editorResult.isErr()) {
        return err(editorResult.error);
    }

    const doc = editorResult.value.document;
    if (doc.languageId !== LANG_TLAPLUS && doc.languageId !== LANG_TLAPLUS_CFG) {
        return err(new ModelCheckingError(
            'File in the active editor is not a .tla or .cfg file, it cannot be checked as a model'
        ));
    }
    return ok(doc.uri);
}

export function getEditorIfCanRunTlc(
    extContext: vscode.ExtensionContext
): Result<vscode.TextEditor, ModelCheckingError> {
    if (!canRunTlc(extContext)) {
        return err(new ModelCheckingError('Cannot run TLC in the current context'));
    }
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        return err(new ModelCheckingError('No editor is active, cannot find a TLA+ model to check'));
    }
    return ok(editor);
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
        lastCheckFiles = specFiles;
        vscode.commands.executeCommand('setContext', CTX_TLC_CAN_RUN_AGAIN, true);
        updateStatusBarItem(true);
        const procInfo = await runTlc(
            specFiles.tlaFilePath, path.basename(specFiles.cfgFilePath), showOptionsPrompt, extraOpts);
        if (procInfo === undefined) {
            // Command cancelled by user
            return undefined;
        }
        outChannel.bindTo(procInfo);
        checkProcess = procInfo.process;
        checkProcess.on('close', () => {
            checkProcess = undefined;
            updateStatusBarItem(false);
        });
        if (showCheckResultView) {
            attachFileSaver(specFiles.tlaFilePath, checkProcess);
            revealEmptyCheckResultView(ModelCheckResultSource.Process, extContext);
        }
        const resultHolder = new CheckResultHolder();
        const checkResultCallback = (checkResult: ModelCheckResult) => {
            resultHolder.checkResult = checkResult;
            if (showCheckResultView) {
                updateCheckResultView(checkResult);
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
        vscode.window.showErrorMessage(err.message);
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
    const cleanLine = line.replace(/@!@!@(START|END)MSG \d+(:\d+)? @!@!@/g, '');
    return cleanLine === '' ? undefined : cleanLine;
}
