import * as vscode from 'vscode';
import * as fs from 'fs';
import { PassThrough, Readable } from 'stream';
import { TLCModelCheckerStdoutParser } from '../parsers/tlc';
import { revealCheckResultView, revealEmptyCheckResultView, updateCheckResultView } from '../checkResultView';

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
        showOutput(filePath, data, extContext);
    });
}

function showOutput(outFilePath: string, buffer: Buffer, extContext: vscode.ExtensionContext) {
    const stream = new PassThrough();
    stream.end(buffer);
    revealEmptyCheckResultView(extContext);
    const parser = new TLCModelCheckerStdoutParser(stream, undefined, outFilePath, updateCheckResultView);
    parser.readAll();
}
