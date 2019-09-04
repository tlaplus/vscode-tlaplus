import * as vscode from 'vscode';
import * as fs from 'fs';
import { PassThrough } from 'stream';
import { TlcModelCheckerStdoutParser } from '../parsers/tlc';
import { revealEmptyCheckResultView, updateCheckResultView } from '../checkResultView';
import { ModelCheckResultSource } from '../model/check';

export const CMD_VISUALIZE_TLC_OUTPUT = 'tlaplus.out.visualize';

/**
 * Opens a panel with visualization of the TLC output file (.out).
 */
export function visualizeTlcOutput(extContext: vscode.ExtensionContext) {
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
        showOutput(data, extContext);
    });
}

function showOutput(buffer: Buffer, extContext: vscode.ExtensionContext) {
    const stream = new PassThrough();
    stream.end(buffer);
    revealEmptyCheckResultView(ModelCheckResultSource.OutFile, extContext);
    const parser = new TlcModelCheckerStdoutParser(
        ModelCheckResultSource.OutFile, stream, undefined, false, updateCheckResultView);
    parser.readAll();
}
