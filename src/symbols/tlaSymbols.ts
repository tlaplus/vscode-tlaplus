import * as vscode from 'vscode';
import { TlaDocumentInfos } from '../model/documentInfo';

const COMMA_LEN = 1;
export const ROOT_SYMBOL_NAME = '';
export const PLUS_CAL_SYMBOL_NAME = 'PlusCal algorithm';

enum SpecialSymbol {
    PlusCalEnd
}

class ParsingContext {
    moduleName: string | undefined;
    lastTopDefBlock: vscode.SymbolInformation | undefined;
    plusCal: vscode.SymbolInformation | undefined;
    symbols: vscode.SymbolInformation[] = [];
    plusCalSymbols: vscode.SymbolInformation[] = [];
    plusCalRange: vscode.Range | undefined;
    simpleListSymbolKind: vscode.SymbolKind | undefined;

    getContainerName(): string {
        if (this.plusCal) {
            return this.plusCal.name;
        }
        return this.moduleName || ROOT_SYMBOL_NAME;
    }

    addSymbol(symbol: vscode.SymbolInformation) {
        if (this.plusCal) {
            this.plusCalSymbols.push(symbol);
        } else {
            this.symbols.push(symbol);
        }
    }
}

/**
 * Provides TLA+ symbols from the given document.
 */
export class TlaDocumentSymbolsProvider implements vscode.DocumentSymbolProvider {
    constructor(
        private readonly docInfos: TlaDocumentInfos
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
        const docInfo = this.docInfos.get(document.uri);
        // We only put TLA+ symbols to DocInfos, not PlusCal to exclude duplications on code completion
        docInfo.symbols = context.symbols.filter((s) => s.name !== PLUS_CAL_SYMBOL_NAME);
        docInfo.plusCalSymbols = context.plusCalSymbols;
        docInfo.plusCalRange = context.plusCalRange;
        return context.symbols.concat(context.plusCalSymbols);
    }

    tryExtractSymbol(
        context: ParsingContext,
        document: vscode.TextDocument,
        line: vscode.TextLine
    ): boolean {
        if (typeof context.simpleListSymbolKind !== 'undefined') {
            if (this.tryCollectListItems(context, document.uri, line.lineNumber, 0, line.text)) {
                return true;
            }
        }
        if (!context.moduleName) {
            if (this.tryExtractModuleName(context, document, line)) {
                return true;
            }
        }
        if (this.tryExtractDefinition(context, document, line)) {
            return true;
        }
        if (this.tryExtractListStart(context, document.uri, line)) {
            return true;
        }
        if (this.tryExtractTheoremAxiomLemma(context, document.uri, line)) {
            return true;
        }
        if (this.tryExtractPlusCalStart(context, document.uri, line)) {
            return true;
        }
        return false;
    }

    tryExtractSpecialSymbol(context: ParsingContext, line: vscode.TextLine): boolean {
        const symbol = this.tryExtractPlusCalEnd(line);
        if (typeof symbol === 'undefined') {
            return false;
        }
        if (symbol === SpecialSymbol.PlusCalEnd && context.plusCal) {
            const range = new vscode.Range(context.plusCal.location.range.start, line.range.end);
            context.plusCal.location = new vscode.Location(context.plusCal.location.uri, range);
            context.plusCalRange = range;
            context.plusCal = undefined;
        }
        return true;
    }

    tryExtractModuleName(
        context: ParsingContext,
        document: vscode.TextDocument,
        line: vscode.TextLine
    ): boolean {
        const matches = /^\s*-{4,}\s*MODULE\s*(\w+)\s*-{4,}.*$/g.exec(line.text);
        if (!matches) {
            return false;
        }
        const lastLine = document.lineAt(document.lineCount - 1);
        const symbol = new vscode.SymbolInformation(
            matches[1],
            vscode.SymbolKind.Module,
            ROOT_SYMBOL_NAME,
            new vscode.Location(
                document.uri,
                new vscode.Range(line.range.start, lastLine.range.end)
            )
        );
        context.addSymbol(symbol);
        context.moduleName = symbol.name;
        return true;
    }

    tryExtractDefinition(
        context: ParsingContext,
        document: vscode.TextDocument,
        line: vscode.TextLine
    ): boolean {
        const matches = /^((?:\s*|LET|\/\\)+)(\w+)\s*([(|[)].*)?\s*==\s*(.*)?/g.exec(line.text);
        if (!matches) {
            return false;
        }
        const space = matches[1];
        const name = matches[2];
        if (space.length > 0
            && name.charAt(0).toLowerCase() === name.charAt(0)
            && context.lastTopDefBlock
            && line.range.start.line >= context.lastTopDefBlock.location.range.start.line
            && line.range.end.line <= context.lastTopDefBlock.location.range.end.line
        ) {
            // This looks like a private variable within a top level definition
            context.addSymbol(new vscode.SymbolInformation(
                name,
                vscode.SymbolKind.Variable,
                context.lastTopDefBlock.name,
                new vscode.Location(document.uri, line.range.start)
            ));
            return true;
        }
        // This is a top level definition
        let kind = vscode.SymbolKind.Field;
        const next = matches[3];
        const value = matches[4];
        if (next && (next[0] === '(' || next[0] === '[')) {
            kind = vscode.SymbolKind.Function;
        } else if (value && value.startsWith('INSTANCE')) {
            kind = vscode.SymbolKind.Namespace;
        }
        const blockEnd = findBlockDefinitionEnd(document, line).range.end;
        const symbol = new vscode.SymbolInformation(
            name,
            kind,
            context.getContainerName(),
            new vscode.Location(document.uri, new vscode.Range(line.range.start, blockEnd))
        );
        context.addSymbol(symbol);
        context.lastTopDefBlock = symbol;
        return true;
    }

    tryExtractListStart(
        context: ParsingContext,
        docUri: vscode.Uri,
        line: vscode.TextLine
    ): boolean {
        const matches = /^(\s*)(VARIABLE(?:S)?|CONSTANT(?:S)?)(\s*.*)/g.exec(line.text);
        if (!matches) {
            return false;
        }
        context.simpleListSymbolKind = matches[2].startsWith('V')
            ? vscode.SymbolKind.Variable
            : vscode.SymbolKind.Constant;
        const startIdx = matches[1].length + matches[2].length;
        return this.tryCollectListItems(context, docUri, line.lineNumber, startIdx, matches[3]);
    }

    tryCollectListItems(
        context: ParsingContext,
        docUri: vscode.Uri,
        lineNum: number,
        startChar: number,
        text: string
    ): boolean {
        if (!context.simpleListSymbolKind) {
            return false;
        }
        let charIdx = startChar;
        const chunks = text.split(',');
        let name: string | undefined;
        for (const chunk of chunks) {
            const rChunk = chunk.trimLeft();
            if (isCommentStart(rChunk)) {
                return true;
            }
            charIdx += chunk.length - rChunk.length;    // + number of trimmed spaces
            const matches = /^(\w*)(\s*)(.*)$/g.exec(rChunk);
            if (!matches) {
                context.simpleListSymbolKind = undefined;
                return false;
            }
            name = matches[1];
            const spaces = matches[2];
            const rest = matches[3];
            if (name === '') {
                charIdx += COMMA_LEN;
                continue;
            }
            if (rest !== '' && !isCommentStart(rest)) {
                context.simpleListSymbolKind = undefined;
                return false;
            }
            context.addSymbol(new vscode.SymbolInformation(
                name,
                context.simpleListSymbolKind,
                context.getContainerName(),
                new vscode.Location(docUri, new vscode.Position(lineNum, charIdx))
            ));
            charIdx += name.length + spaces.length + COMMA_LEN;
            if (rest !== '') {
                context.simpleListSymbolKind = undefined;
                break;      // There were no comma after the name
            }
        }
        if (name !== '') {
            context.simpleListSymbolKind = undefined;   // There were no comma after the last name
        }
        return true;
    }

    tryExtractTheoremAxiomLemma(
        context: ParsingContext,
        docUri: vscode.Uri,
        line: vscode.TextLine
    ): boolean {
        const matches = /^\s*(?:THEOREM|AXIOM|LEMMA)\s*(\w+)\s*==/g.exec(line.text);
        if (!matches) {
            return false;
        }
        context.addSymbol(new vscode.SymbolInformation(
            matches[1],
            vscode.SymbolKind.Boolean,
            context.getContainerName(),
            new vscode.Location(docUri, line.range.start)
        ));
        return true;
    }

    tryExtractPlusCalStart(
        context: ParsingContext,
        docUri: vscode.Uri,
        line: vscode.TextLine
    ): boolean {
        const matches = /(\(\*.*)--((?:fair\s+)?algorithm)\b/g.test(line.text);
        if (!matches) {
            return false;
        }
        const symbol = new vscode.SymbolInformation(
            PLUS_CAL_SYMBOL_NAME,
            vscode.SymbolKind.Namespace,
            context.getContainerName(),
            new vscode.Location(docUri, line.range.start)
        );
        context.addSymbol(symbol);
        context.plusCal = symbol;
        return true;
    }

    tryExtractPlusCalEnd(line: vscode.TextLine): SpecialSymbol | undefined {
        const matches = /(end\s+algorithm)(;)?\s*(\*\))/g.test(line.text);
        if (matches) {
            return SpecialSymbol.PlusCalEnd;
        }
        return line.text === '\\* BEGIN TRANSLATION' ? SpecialSymbol.PlusCalEnd : undefined;
    }
}

function isCommentStart(str: string): boolean {
    return str.startsWith('\\*') || str.startsWith('(*');
}

/**
 * Finds and returns the last line of the definition block, started at the given line.
 * Definition block expands till the next non-empty line with no leading spaces.
 */
function findBlockDefinitionEnd(document: vscode.TextDocument, startLine: vscode.TextLine): vscode.TextLine {
    let lastLine = startLine;
    for (let i = startLine.lineNumber + 1; i < document.lineCount; i++) {
        const line = document.lineAt(i);
        if (line.isEmptyOrWhitespace) {
            continue;
        }
        if (line.firstNonWhitespaceCharacterIndex === 0) {      // New block started
            break;
        }
        lastLine = line;
    }
    return lastLine;
}
