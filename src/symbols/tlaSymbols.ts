import * as vscode from 'vscode';
import { TlaDocumentInfos } from '../model/documentInfo';

export const ROOT_SYMBOL_NAME = '';
export const PLUS_CAL_SYMBOL_NAME = 'PlusCal algorithm';

enum SpecialSymbol {
    PlusCalEnd
}

class ParsingContext {
    public moduleName = ROOT_SYMBOL_NAME;
    public plusCal: vscode.SymbolInformation | undefined;
    public symbols: vscode.SymbolInformation[] = [];
    public plusCalSymbols: vscode.SymbolInformation[] = [];
}

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
        const context = new ParsingContext();
        for (let i = 0; i < document.lineCount; i++) {
            const line = document.lineAt(i);
            if (line.isEmptyOrWhitespace) {
                continue;
            }
            const sym = this.tryExtractSymbol(context, document, line);
            if (!sym) {
                this.tryExtractSpecialSymbol(context, line);
            }
        }
        // We only put TLA+ symbols to DocInfos, not PlusCal to exclude duplications on code completion
        this.docInfos.get(document.uri).setSymbols(context.symbols);
        return context.symbols.concat(context.plusCalSymbols);
    }

    tryExtractSymbol(
        context: ParsingContext,
        document: vscode.TextDocument,
        line: vscode.TextLine
    ): boolean {
        let symbol;
        const containerName = context.plusCal ? context.plusCal.name : context.moduleName;
        if (context.moduleName === ROOT_SYMBOL_NAME) {
            symbol = this.tryExtractModuleName(document, line);
            if (symbol) {
                context.moduleName = symbol.name;
            }
        }
        if (!symbol) {
            symbol = this.tryExtractDefinition(document.uri, line, containerName);
        }
        if (!symbol) {
            symbol = this.tryExtractTheoremAxiomLemma(document.uri, line, containerName);
        }
        if (!symbol) {
            symbol = this.tryExtractPlusCalStart(document.uri, line, containerName);
            if (symbol) {
                context.plusCal = symbol;
            }
        }
        if (!symbol) {
            return false;
        }
        if (containerName === PLUS_CAL_SYMBOL_NAME) {
            context.plusCalSymbols.push(symbol);
        } else {
            context.symbols.push(symbol);
        }
        return true;
    }

    tryExtractSpecialSymbol(context: ParsingContext, line: vscode.TextLine): boolean {
        const symbol = this.tryExtractPlusCalEnd(line);
        if (typeof symbol === 'undefined') {
            return false;
        }
        if (symbol === SpecialSymbol.PlusCalEnd && context.plusCal) {
            context.plusCal.location = new vscode.Location(
                context.plusCal.location.uri,
                new vscode.Range(context.plusCal.location.range.start, line.range.end)
            );
            context.plusCal = undefined;
        }
        return true;
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
            new vscode.Location(docUri, line.range.start)
        );
    }

    tryExtractTheoremAxiomLemma(
        docUri: vscode.Uri,
        line: vscode.TextLine,
        moduleName: string
    ): vscode.SymbolInformation | undefined {
        const matches = /^\s*(?:THEOREM|AXIOM|LEMMA)\s*(\w+)\s*==/g.exec(line.text);
        if (!matches) {
            return undefined;
        }
        return new vscode.SymbolInformation(
            matches[1],
            vscode.SymbolKind.Boolean,
            moduleName,
            new vscode.Location(docUri, line.range.start)
        );
    }

    tryExtractPlusCalStart(
        docUri: vscode.Uri,
        line: vscode.TextLine,
        moduleName: string
    ): vscode.SymbolInformation | undefined {
        const matches = /(\(\*.*)--((?:fair\s+)?algorithm)\b/g.test(line.text);
        if (!matches) {
            return undefined;
        }
        return new vscode.SymbolInformation(
            PLUS_CAL_SYMBOL_NAME,
            vscode.SymbolKind.Namespace,
            moduleName,
            new vscode.Location(docUri, line.range.start)
        );
    }

    tryExtractPlusCalEnd(line: vscode.TextLine): SpecialSymbol | undefined {
        const matches = /(end\s+algorithm)(;)?\s*(\*\))/g.test(line.text);
        return matches ? SpecialSymbol.PlusCalEnd : undefined;
    }
}
