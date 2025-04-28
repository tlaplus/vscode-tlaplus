import * as vscode from 'vscode';
import { parseSpec, transpilePlusCal } from '../commands/parseModule';
import { LANG_TLAPLUS } from '../common';
import { applyDCollection } from '../diagnostic';
import { TLADocumentSymbolProvider } from '../symbols/tlaSymbols';
import { TlaDocumentInfos } from '../model/documentInfo';

export interface FileParameter {
	fileName: string;
}

export class ParseModuleTool implements vscode.LanguageModelTool<FileParameter> {
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
            // Transpile PlusCal to TLA+ (if any), and parse the resulting TLA+ spec.
            const messages = await transpilePlusCal(fileUri);
            const specData = await parseSpec(fileUri);
            // Post-process SANY's parse results.
            messages.addAll(specData.dCollection);
            const diagnostic = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
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
                    return new vscode.LanguageModelTextPart(
                        `Parsing of file ${msg.filePath} failed at line ${msg.diagnostic.range.start.line} with 
						error '${msg.diagnostic.message}'`);
                }));
            }
        } catch (err) {
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
