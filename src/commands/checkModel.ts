import * as vscode from 'vscode';
import { runTool } from '../tla2tools';
import { TLCModelCheckerStdoutParser } from '../parsers/tlc';
import { revealCheckResultView, updateCheckResultView } from '../checkResultView';
import { applyDCollection } from '../diagnostic';

/**
 * Runs TLC on a TLA+ specification.
 */
export function checkModel(diagnostic: vscode.DiagnosticCollection) {
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
    doCheckModel(editor.document.uri, diagnostic);
}

async function doCheckModel(fileUri: vscode.Uri, diagnostic: vscode.DiagnosticCollection) {
    try {
        const proc = runTool('tlc2.TLC', fileUri.fsPath, ['-modelcheck', '-coverage', '1', '-tool']);
        revealCheckResultView(null);
        const stdoutParser = new TLCModelCheckerStdoutParser(proc.stdout, fileUri.fsPath, updateCheckResultView);
        const dCol = await stdoutParser.readAll();
        applyDCollection(dCol, diagnostic);
    } catch (e) {
        vscode.window.showErrorMessage(e.message);
    }
}
