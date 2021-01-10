import * as vscode from 'vscode';
import { DCollection, applyDCollection } from '../diagnostic';
import { TranspilerStdoutParser } from '../parsers/pluscal';
import { SanyData, SanyStdoutParser } from '../parsers/sany';
import { runPlusCal, runSany } from '../tla2tools';
import { ToolOutputChannel } from '../outputChannels';
import { LANG_TLAPLUS } from '../common';

export const CMD_PARSE_MODULE = 'tlaplus.parse';

const plusCalOutChannel = new ToolOutputChannel('PlusCal');
const sanyOutChannel = new ToolOutputChannel('SANY');

/**
 * Parses .tla module:
 * - Transpiles PlusCal to TLA+
 * - Parses resulting TLA+ specification and checks for syntax errors
 */
export function parseModule(diagnostic: vscode.DiagnosticCollection): void {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ file to transpile');
        return;
    }
    if (editor.document.languageId !== LANG_TLAPLUS) {
        vscode.window.showWarningMessage('File in the active editor is not a TLA+ file, it cannot be transpiled');
        return;
    }
    editor.document.save().then(() => doParseFile(editor.document, diagnostic));
}

async function doParseFile(doc: vscode.TextDocument, diagnostic: vscode.DiagnosticCollection) {
    try {
        const messages = await transpilePlusCal(doc.uri);
        vscode.window.showTextDocument(doc);    // To force changes reloading
        const specData = await parseSpec(doc.uri);
        messages.addAll(specData.dCollection);
        applyDCollection(messages, diagnostic);
    } catch (e) {
        vscode.window.showErrorMessage(e.message);
    }
}

/**
 * Transpiles PlusCal code in the current .tla file to TLA+ code in the same file.
 */
async function transpilePlusCal(fileUri: vscode.Uri): Promise<DCollection> {
    const procInfo = await runPlusCal(fileUri.fsPath);
    plusCalOutChannel.bindTo(procInfo);
    const stdoutParser = new TranspilerStdoutParser(procInfo.process.stdout, fileUri.fsPath);
    return stdoutParser.readAll();
}

async function adaptMonolithMessages(sanyResult : SanyData) {
    const invertedModulePaths = new Map(Array.from(sanyResult.modulePaths, (i) => i.reverse() as [string, string]));
    for (const [filePath, monolithFilePath] of sanyResult.filePathToMonolithFilePath) {
        const text = (await vscode.workspace.openTextDocument(monolithFilePath)).getText();
        const specName = invertedModulePaths.get(filePath);
        text.split('\n').forEach(function (line, number) {
            if (new RegExp(`-----*\\s*MODULE\\s+${specName}\\s*----*`).exec(line)) {
                sanyResult.dCollection.getMessages().filter(m => m.filePath === filePath).forEach(message => {
                    const oldRange = message.diagnostic.range;
                    // Remove message so it does not appear duplicated in the output.
                    sanyResult.dCollection.removeMessage(message);
                    sanyResult.dCollection.addMessage(
                        monolithFilePath, 
                        new vscode.Range(oldRange.start.line + number, oldRange.start.character, oldRange.end.line + number, oldRange.end.character),
                        message.diagnostic.message,
                        message.diagnostic.severity);
                })
            } 
        });
    }
}

/**
 * Parses the resulting TLA+ spec.
 */
async function parseSpec(fileUri: vscode.Uri): Promise<SanyData> {
    const procInfo = await runSany(fileUri.fsPath);
    sanyOutChannel.bindTo(procInfo);
    const stdoutParser = new SanyStdoutParser(procInfo.process.stdout);
    const sanyResult = await stdoutParser.readAll();
    // Adapt monolith error locations.
    // It modifies the Sany result adding the module offset for in the monolith spec.
    await adaptMonolithMessages(sanyResult);
    return sanyResult;
}
