import * as fs from 'fs';
import { PassThrough } from 'stream';
import * as vscode from 'vscode';
import { ModelCheckResultSource } from '../model/check';
import { CheckResultViewController } from '../panels/checkResultView';
import { TlcModelCheckerStdoutParser } from '../parsers/tlc';

export const CMD_VISUALIZE_TLC_OUTPUT = 'tlaplus.out.visualize';

/**
 * Opens a panel with visualization of the TLC output file (.out).
 */
export function visualizeTlcOutput(
    _extContext: vscode.ExtensionContext,
    checkResultView: CheckResultViewController,
): void {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find an .out file to visualize');
        return;
    }
    const filePath = editor.document.fileName;
    if (!filePath.endsWith('.out')) {
        vscode.window.showWarningMessage(
            'File in the active editor is not an .out file, it cannot be visualized');
        return;
    }
    fs.readFile(filePath, (err, data) => {
        if (err) {
            vscode.window.showErrorMessage(`Cannot read file: ${err}`);
            return;
        }
        showOutput(data, checkResultView);
    });
}

function showOutput(buffer: Buffer, checkResultView: CheckResultViewController) {
    const stream = new PassThrough();
    stream.end(buffer);
    checkResultView.revealEmpty();
    const parser = new TlcModelCheckerStdoutParser(
        ModelCheckResultSource.OutFile, stream, undefined, false, (checkResult) => checkResultView.updateCheckResult(checkResult));
    void parser.readAll();
}
