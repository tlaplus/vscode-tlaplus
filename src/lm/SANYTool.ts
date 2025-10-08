import * as vscode from 'vscode';
import { parseSpec, transpilePlusCal } from '../commands/parseModule';
import { applyDCollection } from '../diagnostic';
import { TLADocumentSymbolProvider } from '../symbols/tlaSymbols';
import { TlaDocumentInfos } from '../model/documentInfo';
import { getDiagnostic } from '../main';

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
            // Transpile PlusCal to TLA+ (if any), and parse the resulting TLA+ spec.
            const messages = await transpilePlusCal(fileUri, token);
            throwIfCancelled();
            const specData = await parseSpec(fileUri, token);
            throwIfCancelled();
            // Post-process SANY's parse results.
            messages.addAll(specData.dCollection);
            const diagnostic = getDiagnostic();
            applyDCollection(messages, diagnostic);
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
            const symbols = await tdsp.provideDocumentSymbols(document, token);

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
