import * as vscode from 'vscode';
import { DCollection, applyDCollection } from '../diagnostic';
import { TranspilerStdoutParser } from '../parsers/pluscal';
import { SanyData, SanyStdoutParser, getDivergenceType, hasTranslationChecksums } from '../parsers/sany';
import { runPlusCal, runSany, stopProcess, ToolProcessInfo } from '../tla2tools';
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

const OVERWRITE_PCAL_TRANSL_LABEL = 'Overwrite Translation';

async function doParseFile(doc: vscode.TextDocument, diagnostic: vscode.DiagnosticCollection) {
    try {
        // Only run the pre-translation SANY check if the file has translation markers with checksums.
        // This avoids doubling SANY invocations for files without PlusCal or without checksums.
        if (hasTranslationChecksums(doc.getText())) {
            const initialSpecData = await parseSpec(doc.uri);
            const divergence = getDivergenceType(initialSpecData);
            if (divergence === 'tla' || divergence === 'both') {
                const choice = await vscode.window.showWarningMessage(
                    'A hash mismatch has been found that indicates that the TLA+ translation has been modified '
                    + 'manually since its last translation. Click "Overwrite Translation" to replace the TLA+ '
                    + 'translation anyway or "Cancel" to abort re-translation and keep the modified TLA+ translation.',
                    OVERWRITE_PCAL_TRANSL_LABEL,
                    'Cancel'
                );
                if (choice !== OVERWRITE_PCAL_TRANSL_LABEL) {
                    // User cancelled — apply initial SANY diagnostics without translating
                    applyDCollection(initialSpecData.dCollection, diagnostic);
                    return;
                }
            }
        }
        const messages = await transpilePlusCal(doc.uri);
        vscode.window.showTextDocument(doc);    // To force changes reloading
        const specData = await parseSpec(doc.uri);
        messages.addAll(specData.dCollection);
        applyDCollection(messages, diagnostic);
    } catch (err) {
        vscode.window.showErrorMessage(`Error parsing file: ${err}`);
    }
}

/**
 * Transpiles PlusCal code in the current .tla file to TLA+ code in the same file.
 */
export async function transpilePlusCal(fileUri: vscode.Uri, token?: vscode.CancellationToken): Promise<DCollection> {
    throwIfCancelled(token);
    const procInfo = await runPlusCal(fileUri.fsPath);
    plusCalOutChannel.bindTo(procInfo);
    const cancellationDisposable = registerCancellation(procInfo, token);
    const stdoutParser = new TranspilerStdoutParser(procInfo.mergedOutput, fileUri.fsPath);
    try {
        const result = await stdoutParser.readAll();
        throwIfCancelled(token);
        return result;
    } finally {
        cancellationDisposable?.dispose();
    }
}

/**
 * Parses the resulting TLA+ spec.
 */
export async function parseSpec(fileUri: vscode.Uri, token?: vscode.CancellationToken): Promise<SanyData> {
    throwIfCancelled(token);
    const procInfo = await runSany(fileUri.fsPath);
    sanyOutChannel.bindTo(procInfo);
    const cancellationDisposable = registerCancellation(procInfo, token);
    const stdoutParser = new SanyStdoutParser(procInfo.mergedOutput);
    try {
        const result = await stdoutParser.readAll();
        throwIfCancelled(token);
        return result;
    } finally {
        cancellationDisposable?.dispose();
    }
}

function throwIfCancelled(token: vscode.CancellationToken | undefined): void {
    if (token?.isCancellationRequested) {
        throw new vscode.CancellationError();
    }
}

function registerCancellation(
    procInfo: ToolProcessInfo,
    token: vscode.CancellationToken | undefined
): vscode.Disposable | undefined {
    if (!token) {
        return undefined;
    }
    const cancel = () => stopProcess(procInfo.process);
    if (token.isCancellationRequested) {
        cancel();
        return undefined;
    }
    return token.onCancellationRequested(cancel);
}
