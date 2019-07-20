import * as vscode from 'vscode';
import { DCollection } from '../diagnostic';
import { TranspilerStdoutParser } from '../parsers/pluscal';
import { SanyStdoutParser } from '../parsers/sany';
import { runTool } from '../tla2tools';

// TODO: handle exit codes in parsers

/**
 * Parses .tla module:
 * - Transpiles PlusCal to TLA+
 * - Parses resulting TLA+ specification and checks for syntax errors
 */
export function parseModule(diagnostic: vscode.DiagnosticCollection) {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ file to transpile');
        return;
    }
    if (editor.document.languageId !== 'tlaplus') {
        vscode.window.showWarningMessage('File in the active editor is not a TLA+ file, it cannot be transpiled');
        return;
    }
    editor.document.save().then(() => doParseFile(editor.document.uri, diagnostic));
}

async function doParseFile(fileUri: vscode.Uri, diagnostic: vscode.DiagnosticCollection) {
    try {
        const messages = await transpilePlusCal(fileUri);
        const specMessages = await parseSpec(fileUri);
        messages.addAll(specMessages);
        messages.apply(diagnostic);
    } catch (e) {
        vscode.window.showErrorMessage(e.message);
    }
}

/**
 * Transpiles PlusCal code in the current .tla file to TLA+ code in the same file.
 */
async function transpilePlusCal(fileUri: vscode.Uri): Promise<DCollection> {
    const proc = runTool('pcal.trans', fileUri.fsPath);
    const stdoutParser = new TranspilerStdoutParser(proc.stdout, fileUri.fsPath);
    return stdoutParser.readAll();
}

/**
 * Parses the resulting TLA+ spec.
 */
async function parseSpec(fileUri: vscode.Uri): Promise<DCollection> {
    const proc = runTool('tla2sany.SANY', fileUri.fsPath);
    const stdoutParser = new SanyStdoutParser(proc.stdout);
    return stdoutParser.readAll();
}
