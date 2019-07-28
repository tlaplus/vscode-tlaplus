import * as vscode from 'vscode';
import { runTool } from '../tla2tools';
import { TLCModelCheckerStdoutParser } from '../parsers/tlc';
import { revealCheckResultView, updateCheckResultView, revealEmptyCheckResultView } from '../checkResultView';
import { applyDCollection } from '../diagnostic';
import { ChildProcess } from 'child_process';

export const CMD_CHECK_MODEL = 'tlaplus.model.check';
export const CMD_CHECK_MODEL_DISPLAY = 'tlaplus.model.check.display';

let checkProcess: ChildProcess | undefined;
const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);

/**
 * Runs TLC on a TLA+ specification.
 */
export function checkModel(diagnostic: vscode.DiagnosticCollection, extContext: vscode.ExtensionContext) {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ model to check');
        return;
    }
    if (editor.document.languageId !== 'tlaplus') {
        vscode.window.showWarningMessage(
            'File in the active editor is not a TLA+ file, it cannot be checked as a model');
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

async function doCheckModel(
    fileUri: vscode.Uri,
    extContext: vscode.ExtensionContext,
    diagnostic: vscode.DiagnosticCollection
) {
    try {
        showStatusBarItem();
        checkProcess = runTool('tlc2.TLC', fileUri.fsPath, ['-modelcheck', '-coverage', '1', '-tool']);
        checkProcess.on('close', () => {
            checkProcess = undefined;
        });
        revealEmptyCheckResultView(extContext);
        const stdoutParser = new TLCModelCheckerStdoutParser(
            checkProcess.stdout, fileUri.fsPath, updateCheckResultView);
        const dCol = await stdoutParser.readAll();
        applyDCollection(dCol, diagnostic);
    } catch (e) {
        statusBarItem.hide();
        vscode.window.showErrorMessage(e.message);
    }
}

function showStatusBarItem() {
    statusBarItem.text = 'TLC';
    statusBarItem.tooltip = 'TLA+ model checking is in progress';
    statusBarItem.command = CMD_CHECK_MODEL_DISPLAY;
    statusBarItem.show();
}
