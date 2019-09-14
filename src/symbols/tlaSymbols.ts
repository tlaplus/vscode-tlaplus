import * as vscode from 'vscode';
import { TlaDocumentInfos } from '../model/documentInfo';

export const ROOT_SYMBOL_NAME = '';

/**
 * Provides TLA+ symbols from the given document.
 */
export class TlaDocumentSymbolsProvider implements vscode.DocumentSymbolProvider {
    constructor(
        private docInfos: TlaDocumentInfos
    ) {}

    provideDocumentSymbols(
        document: vscode.TextDocument,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.SymbolInformation[] | vscode.DocumentSymbol[]> {
        const symbols = [];
        let moduleName = ROOT_SYMBOL_NAME;
        for (let i = 0; i < document.lineCount; i++) {
            const symbol = this.tryExtractSymbol(document, document.lineAt(i), moduleName);
            if (!symbol) {
                continue;
            }
            if (!moduleName && symbol.kind === vscode.SymbolKind.Module) {
                moduleName = symbol.name;
            }
            symbols.push(symbol);
        }
        this.docInfos.get(document.uri).setSymbols(symbols);
        return symbols;
    }

    tryExtractSymbol(
        document: vscode.TextDocument,
        line: vscode.TextLine,
        moduleName: string
    ): vscode.SymbolInformation | undefined {
        if (line.isEmptyOrWhitespace) {
            return undefined;
        }
        let symbol;
        if (moduleName === ROOT_SYMBOL_NAME) {
            symbol = this.tryExtractModuleName(document, line);
        }
        if (!symbol) {
            symbol = this.tryExtractDefinition(document.uri, line, moduleName);
        }
        if (!symbol) {
            symbol = this.tryExtractTheoremAxiom(document.uri, line, moduleName);
        }
        return symbol;
    }

    tryExtractModuleName(
        document: vscode.TextDocument,
        line: vscode.TextLine
    ): vscode.SymbolInformation | undefined {
        const matches = /^\s*-{4,}\s*MODULE\s*(\w+)\s*-{4,}.*$/g.exec(line.text);
        if (!matches) {
            return undefined;
        }
        const lastLine = document.lineAt(document.lineCount - 1);
        return new vscode.SymbolInformation(
            matches[1],
            vscode.SymbolKind.Module,
            '',
            new vscode.Location(
                document.uri,
                new vscode.Range(line.range.start, lastLine.range.end)
            )
        );
    }

    tryExtractDefinition(
        docUri: vscode.Uri,
        line: vscode.TextLine,
        moduleName: string
    ): vscode.SymbolInformation | undefined {
        const matches = /^\s*(\w+)\s*([\(|\[)].*)?\s*==\s*(.*)?/g.exec(line.text);
        if (!matches) {
            return undefined;
        }
        let kind = vscode.SymbolKind.Field;
        const next = matches[2];
        const value = matches[3];
        if (next && (next[0] === '(' || next[0] === '[')) {
            kind = vscode.SymbolKind.Function;
        } else if (value && value.startsWith('INSTANCE')) {
            kind = vscode.SymbolKind.Namespace;
        }
        return new vscode.SymbolInformation(
            matches[1],
            kind,
            moduleName,
            new vscode.Location(docUri, line.range)
        );
    }

    tryExtractTheoremAxiom(
        docUri: vscode.Uri,
        line: vscode.TextLine,
        moduleName: string
    ): vscode.SymbolInformation | undefined {
        const matches = /^\s*(?:THEOREM|AXIOM)\s*(\w+)\s*==/g.exec(line.text);
        if (!matches) {
            return undefined;
        }
        return new vscode.SymbolInformation(
            matches[1],
            vscode.SymbolKind.Boolean,
            moduleName,
            new vscode.Location(docUri, line.range)
        );
    }
}
