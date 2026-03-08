import * as vscode from 'vscode';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG } from '../common';
import { SpecFiles } from '../model/check';
import { ExtensionRuntime } from '../runtime/extensionRuntime';
import { CheckSession } from '../services/checkService';
import { CheckResultViewController } from '../panels/checkResultView';
import { ModelResolveMode } from './modelResolver';

export const CMD_CHECK_MODEL_RUN = 'tlaplus.model.check.run';
export const CMD_CHECK_MODEL_RUN_AGAIN = 'tlaplus.model.check.runAgain';
export const CMD_CHECK_MODEL_CUSTOM_RUN = 'tlaplus.model.check.customRun';
export const CMD_CHECK_MODEL_STOP = 'tlaplus.model.check.stop';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';
export const CMD_SHOW_TLC_OUTPUT = 'tlaplus.showTlcOutput';
export const CTX_TLC_RUNNING = 'tlaplus.tlc.isRunning';
export const CTX_TLC_CAN_RUN_AGAIN = 'tlaplus.tlc.canRunAgain';

export async function checkModel(
    fileUri: vscode.Uri | undefined,
    runtime: ExtensionRuntime,
    extContext: vscode.ExtensionContext,
    checkResultView: CheckResultViewController
): Promise<void> {
    const uri = fileUri ? fileUri : getActiveEditorFileUri();
    if (!uri) {
        return;
    }

    const specFiles = await runtime.checkService.resolveSpecFiles(uri, true);
    if (!specFiles) {
        return;
    }

    await runCheckSession(specFiles, runtime, extContext, checkResultView, {
        showOptionsPrompt: true,
        showFullOutput: true,
    }, true);
}

export async function runLastCheckAgain(
    runtime: ExtensionRuntime,
    extContext: vscode.ExtensionContext,
    checkResultView: CheckResultViewController
): Promise<void> {
    const lastCheckFiles = runtime.checkService.sessions.lastSpecFiles();
    if (!lastCheckFiles) {
        vscode.window.showWarningMessage('No last check to run');
        return;
    }

    await runCheckSession(lastCheckFiles, runtime, extContext, checkResultView, {
        showOptionsPrompt: false,
        showFullOutput: true,
    }, true);
}

export async function checkModelCustom(
    runtime: ExtensionRuntime,
    extContext: vscode.ExtensionContext,
    checkResultView: CheckResultViewController,
): Promise<void> {
    const editor = getEditorIfCanRunTlc();
    if (!editor) {
        return;
    }
    const doc = editor.document;
    if (doc.languageId !== LANG_TLAPLUS && doc.languageId !== LANG_TLAPLUS_CFG) {
        vscode.window.showWarningMessage(
            'File in the active editor is not a .tla or .cfg, it cannot be checked as a model');
        return;
    }
    const specFiles = await runtime.checkService.resolveSpecFiles(doc.uri, true, true, 'customPick');
    if (!specFiles) {
        return;
    }

    await runCheckSession(specFiles, runtime, extContext, checkResultView, {
        showOptionsPrompt: true,
        showFullOutput: true,
    }, true);
}

export function displayModelChecking(checkResultView: CheckResultViewController): void {
    checkResultView.revealLastResult();
}

export function stopModelChecking(
    runtime: ExtensionRuntime,
    terminateLastRun: (lastSpecFiles: SpecFiles | undefined) => boolean =
        (): boolean => true,
    silent = false
): void {
    const stopped = runtime.checkService.stopLatestSession(
        (session) => terminateLastRun(session.specFiles)
    );
    if (!stopped && !silent) {
        vscode.window.showInformationMessage("There're no currently running model checking processes");
    }
}

export function showTlcOutput(runtime: ExtensionRuntime): void {
    runtime.checkService.revealOutput();
}

export function getEditorIfCanRunTlc(): vscode.TextEditor | undefined {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ model to check');
        return undefined;
    }
    return editor;
}

export async function resolveSpecFiles(
    runtime: ExtensionRuntime,
    fileUri: vscode.Uri,
    warn = true,
    interactive = true,
    mode: ModelResolveMode = 'adjacent'
): Promise<SpecFiles | undefined> {
    return runtime.checkService.resolveSpecFiles(fileUri, warn, interactive, mode);
}

export async function runCheckSession(
    specFiles: SpecFiles,
    runtime: ExtensionRuntime,
    extContext: vscode.ExtensionContext,
    checkResultView: CheckResultViewController,
    request: {
        showOptionsPrompt: boolean;
        showFullOutput?: boolean;
        extraOpts?: string[];
        debuggerPortCallback?: (port?: number) => void;
    },
    showCheckResultView: boolean,
): Promise<CheckSession | undefined> {
    if (showCheckResultView) {
        checkResultView.revealEmpty();
    }

    const session = await runtime.checkService.startSession(specFiles, request);
    if (!session) {
        return undefined;
    }

    await session.completion;
    if (showCheckResultView) {
        await runtime.checkService.maybeGenerateSequenceDiagram(session, extContext);
    }
    return session;
}

function getActiveEditorFileUri(): vscode.Uri | undefined {
    const editor = getEditorIfCanRunTlc();
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
