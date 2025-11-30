import * as vscode from 'vscode';
import { parseSpec, transpilePlusCal } from '../commands/parseModule';
import { DCollection } from '../diagnostic';
import { TLADocumentSymbolProvider } from '../symbols/tlaSymbols';
import { TlaDocumentInfos } from '../model/documentInfo';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { copyLocalTlaModules, remapDiagnostics } from './utils/fs';

export interface FileParameter {
	fileName: string;
}

export class ParseModuleTool implements vscode.LanguageModelTool<FileParameter> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
        token: vscode.CancellationToken
    ) {
        const cancellationResult = (filePath: string) => new vscode.LanguageModelToolResult(
            [new vscode.LanguageModelTextPart(`Parsing cancelled for ${filePath}.`)]
        );
        const throwIfCancelled = () => {
            if (token.isCancellationRequested) {
                throw new vscode.CancellationError();
            }
        };
        // create an URI from the file name and check if the file exists.
        const fileUri = vscode.Uri.file(options.input.fileName);
        if (!fileUri) {
            return new vscode.LanguageModelToolResult(
                [new vscode.LanguageModelTextPart(`File ${options.input.fileName} does not exist`)]);
        }
        if (token.isCancellationRequested) {
            return cancellationResult(fileUri.fsPath);
        }

        try {
            throwIfCancelled();

            // Work on a temporary copy to avoid mutating the user's file. We copy all *.tla files
            // in the source directory so that intra-directory imports still resolve
            const originalDir = path.dirname(fileUri.fsPath);
            const tmpDir = await fs.promises.mkdtemp(path.join(os.tmpdir(), 'tlaplus-sany-'));
            await copyLocalTlaModules(originalDir, tmpDir);
            const tmpUri = vscode.Uri.file(path.join(tmpDir, path.basename(fileUri.fsPath)));

            let messages: DCollection; // PlusCal diagnostics
            let sanyMessages: DCollection; // SANY diagnostics with remapped paths
            try {
                // Transpile PlusCal on the temp copy, but attribute diagnostics to the original file
                // Preserve the caller-provided path casing for diagnostics (important on Windows)
                messages = await transpilePlusCal(tmpUri, token, { diagnosticFilePath: options.input.fileName });
                throwIfCancelled();

                // Parse the translated temp file with SANY
                const specData = await parseSpec(tmpUri, token);
                throwIfCancelled();

                // Remap diagnostics back to the original folder so the user sees their paths, without
                // writing anything to disk
                sanyMessages = remapDiagnostics(specData.dCollection, tmpDir, originalDir);
                messages.addAll(sanyMessages);
            } finally {
                // Always clean up the temp directory
                fs.promises.rm(tmpDir, { recursive: true, force: true }).catch(() => { /* ignore */ });
            }

            // Return summary text; we intentionally avoid touching the workspace diagnostic collection
            // to keep this LM tool side-effect free
            // We are happy if SANY is happy.
            if (messages.messages.length === 0) {
                // If there are no parse failures, return a success message.
                return new vscode.LanguageModelToolResult(
                    [new vscode.LanguageModelTextPart(`No errors found in the TLA+ specification ${fileUri}.`)]);
            } else {
                // Loop over the parse failures in messages.messages and create a new LanguageModelTextPart for
                // each DMessage.
                return new vscode.LanguageModelToolResult(messages.messages.map((msg) => {
                    const line = msg.diagnostic.range.start.line;
                    const textParts = [
                        `Parsing of file ${msg.filePath} failed at line ${line}`,
                        `with error '${msg.diagnostic.message}'`
                    ];
                    return new vscode.LanguageModelTextPart(textParts.join(' '));
                }));
            }
        } catch (err) {
            if (err instanceof vscode.CancellationError) {
                return cancellationResult(fileUri.fsPath);
            }
            return new vscode.LanguageModelToolResult([new vscode.LanguageModelTextPart(`Parsing failed: ${err}`)]);
        }
    }
}

export class SymbolProviderTool implements vscode.LanguageModelTool<FileParameter> {
    async invoke(
        options: vscode.LanguageModelToolInvocationOptions<FileParameter>,
        token: vscode.CancellationToken
    ) {
        // create an URI from the file name and check if the file exists.
        const fileUri = vscode.Uri.file(options.input.fileName);
        if (!fileUri) {
            return new vscode.LanguageModelToolResult(
                [new vscode.LanguageModelTextPart(`File ${options.input.fileName} does not exist`)]);
        }

        try {
            const document = await vscode.workspace.openTextDocument(fileUri);
            const tdsp = new TLADocumentSymbolProvider(new TlaDocumentInfos());
            const symbols = await tdsp.provideGroupedDocumentSymbols(document, token);

            const newLocal = JSON.stringify(symbols, null, 2);
            return new vscode.LanguageModelToolResult([
                new vscode.LanguageModelTextPart(`Document symbols for ${options.input.fileName}:\n${newLocal}`)
            ]);
        } catch (err) {
            return new vscode.LanguageModelToolResult(
                [new vscode.LanguageModelTextPart(`Failed to retrieve document symbols: ${err}`)]);
        }
    }
}
