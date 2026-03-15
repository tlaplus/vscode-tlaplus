import * as vscode from 'vscode';
import { LANG_TLAPLUS } from '../common';
import { ExtensionRuntime } from '../runtime/extensionRuntime';

export const CMD_PARSE_MODULE = 'tlaplus.parse';

/**
 * Parses .tla module:
 * - Transpiles PlusCal to TLA+
 * - Parses resulting TLA+ specification and checks for syntax errors
 */
export function parseModule(runtime: ExtensionRuntime): void {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ file to transpile');
        return;
    }
    if (editor.document.languageId !== LANG_TLAPLUS) {
        vscode.window.showWarningMessage('File in the active editor is not a TLA+ file, it cannot be transpiled');
        return;
    }
    editor.document.save().then(() => doParseFile(editor.document, runtime));
}

async function doParseFile(doc: vscode.TextDocument, runtime: ExtensionRuntime) {
    try {
        const messages = await runtime.parseService.transpilePlusCal(doc.uri);
        vscode.window.showTextDocument(doc);    // To force changes reloading
        const specData = await runtime.parseService.parseSpec(doc.uri);
        messages.addAll(specData.dCollection);
        runtime.diagnosticsProjector.project(messages);
    } catch (err) {
        vscode.window.showErrorMessage(`Error parsing file: ${err}`);
    }
}
