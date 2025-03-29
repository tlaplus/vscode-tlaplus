import * as vscode from 'vscode';
import { Module, TlaDocumentInfo, TlaDocumentInfos } from '../model/documentInfo';

const COMMA_LEN = 1;
export const ROOT_SYMBOL_NAME = '*';
export const ROOT_CONTAINER_NAME = '';
export const PLUS_CAL_DEFAULT_NAME = 'PlusCal algorithm';

enum SpecialSymbol {
    PlusCalEnd
}

/**
 * Holds information about currently parsing module (an actual TLA+ module or PlusCal algorithm)
 */
class ModuleContext {
    readonly symbols: vscode.SymbolInformation[] = [];
    lastTopDefBlock: vscode.SymbolInformation | undefined;
    simpleListSymbolKind: vscode.SymbolKind | undefined;

    constructor(
        readonly rootSymbol: vscode.SymbolInformation,
        readonly containerName = rootSymbol.name
    ) {
        this.symbols.push(rootSymbol);
    }

    addSymbol(symbol: vscode.SymbolInformation) {
        this.symbols.push(symbol);
    }

    close(end: vscode.Position) {
        this.rootSymbol.location.range = new vscode.Range(this.rootSymbol.location.range.start, end);
    }

    convert(): Module {
        return new Module(
            this.rootSymbol.name,
            this.symbols,
            this.rootSymbol.location.range
        );
    }
}

class ParsingContext {
    readonly modules: ModuleContext[] = [];
    readonly rootModule: ModuleContext;  // Collects symbols that are placed outside a TLA+ module and PlusCal algorithm
    plusCal: ModuleContext | undefined;
    currentModule: ModuleContext;

    constructor(document: vscode.TextDocument) {
        const zeroPos = new vscode.Position(0, 0);
        const rootSymbol = new vscode.SymbolInformation(     // Represents the whole document
            ROOT_SYMBOL_NAME,
            vscode.SymbolKind.Namespace,
            ROOT_CONTAINER_NAME,
            new vscode.Location(document.uri, new vscode.Range(zeroPos, zeroPos))
        );
        this.rootModule = new ModuleContext(rootSymbol, '');
        this.currentModule = this.rootModule;
    }

    isInRoot(): boolean {
        return this.currentModule === this.rootModule;
    }

    isInPlusCal(): boolean {
        return this.plusCal && this.currentModule === this.plusCal ? true : false;
    }

    startPlusCal(rootSymbol: vscode.SymbolInformation) {
        this.startModule(rootSymbol, true);
    }

    startModule(rootSymbol: vscode.SymbolInformation, plusCal = false): ModuleContext {
        const module = new ModuleContext(rootSymbol);
        this.modules.push(module);
        this.currentModule = module;
        if (plusCal) {
            this.plusCal = module;
        }
        return module;
    }

    closeModule(end: vscode.Position) {
        if (this.currentModule) {
            this.currentModule.close(end);
            this.currentModule = this.rootModule;
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
        const context = new ParsingContext(document);
        let lastLine = undefined;
        for (let i = 0; i < document.lineCount; i++) {
            const line = document.lineAt(i);
            lastLine = line;
            if (line.isEmptyOrWhitespace) {
                continue;
            }
            const sym = this.tryExtractSymbol(context, document, line);
            if (!sym) {
                this.tryExtractSpecialSymbol(context, line);
            }
        }
        if (context.currentModule && lastLine) {
            context.closeModule(lastLine.range.end);
        }
        let symbols = context.rootModule.symbols.filter(s => s.name !== ROOT_SYMBOL_NAME);
        for (const modCtx of context.modules) {
            symbols = symbols.concat(modCtx.symbols);
        }
        this.docInfos.set(document.uri, new TlaDocumentInfo(
            context.rootModule.convert(),
            context.plusCal?.convert(),
            context.modules.map(m => m.convert()),
            symbols.slice()
        ));
        if (context.plusCal) {
            symbols = symbols.concat(context.plusCal.symbols);
        }
        return symbols;
    }

    tryExtractSymbol(
        context: ParsingContext,
        document: vscode.TextDocument,
        line: vscode.TextLine
    ): boolean {
        const moduleStart = this.tryStartTlaModule(context, document, line);
        if (moduleStart) {
            return true;
        }
        if (context.isInRoot() && this.tryStartPlusCal(context, document.uri, line)) {
            return true;
        }
        if (this.tryEndModule(context, line)) {
            return true;
        }
        const module = context.currentModule;
        if (typeof module.simpleListSymbolKind !== 'undefined') {
            if (this.tryCollectListItems(module, document.uri, line.lineNumber, 0, line.text)) {
                return true;
            }
        }
        if (this.tryExtractDefinition(module, document, line)) {
            return true;
        }
        if (this.tryExtractListStart(module, document.uri, line)) {
            return true;
        }
        if (this.tryExtractTheoremAxiomLemma(module, document.uri, line)) {
            return true;
        }
        return false;
    }

    tryExtractSpecialSymbol(context: ParsingContext, line: vscode.TextLine): boolean {
        const symbol = this.tryExtractPlusCalEnd(line);
        if (typeof symbol === 'undefined') {
            return false;
        }
        if (symbol === SpecialSymbol.PlusCalEnd && context.isInPlusCal()) {
            context.closeModule(line.range.end);
            context.plusCal = undefined;
        }
        return true;
    }

    tryStartTlaModule(
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
            ROOT_CONTAINER_NAME,
            new vscode.Location(
                document.uri,
                new vscode.Range(line.range.start, lastLine.range.end)
            )
        );
        context.startModule(symbol);
        return true;
    }

    tryEndModule(context: ParsingContext, line: vscode.TextLine): boolean {
        const matches = /^={4,}\s*$/g.exec(line.text);
        if (!matches) {
            return false;
        }
        context.closeModule(line.range.end);
        return true;
    }

    tryExtractDefinition(
        module: ModuleContext,
        document: vscode.TextDocument,
        line: vscode.TextLine
    ): boolean {
        const matches = /^((?:\s|LET|\/\\)*)(\w+)\s*([(|[)].*)?\s*==\s*(.*)?/g.exec(line.text);
        if (!matches) {
            return false;
        }
        const prefix = matches[1];
        const name = matches[2];
        const blockStart = new vscode.Position(line.range.start.line, prefix.length);
        const ltp = module.lastTopDefBlock;
        if (ltp
            && line.range.start.line >= ltp.location.range.start.line
            && line.range.end.line <= ltp.location.range.end.line
            && prefix.length > module.rootSymbol.location.range.start.character
        ) {
            // This looks like a private variable within a top level definition
            module.addSymbol(new vscode.SymbolInformation(
                name,
                vscode.SymbolKind.Variable,
                ltp.name,
                new vscode.Location(document.uri, blockStart)
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
        const blockEnd = findBlockDefinitionEnd(document, line, blockStart.character).range.end;
        const symbol = new vscode.SymbolInformation(
            name,
            kind,
            module.containerName,
            new vscode.Location(document.uri, new vscode.Range(blockStart, blockEnd))
        );
        module.addSymbol(symbol);
        module.lastTopDefBlock = symbol;
        return true;
    }

    tryExtractListStart(
        module: ModuleContext,
        docUri: vscode.Uri,
        line: vscode.TextLine
    ): boolean {
        const matches = /^(\s*)(VARIABLE(?:S)?|CONSTANT(?:S)?)(\s*.*)/g.exec(line.text);
        if (!matches) {
            return false;
        }
        module.simpleListSymbolKind = matches[2].startsWith('V')
            ? vscode.SymbolKind.Variable
            : vscode.SymbolKind.Constant;
        const startIdx = matches[1].length + matches[2].length;
        return this.tryCollectListItems(module, docUri, line.lineNumber, startIdx, matches[3]);
    }

    tryCollectListItems(
        module: ModuleContext,
        docUri: vscode.Uri,
        lineNum: number,
        startChar: number,
        text: string
    ): boolean {
        if (!module.simpleListSymbolKind) {
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
                module.simpleListSymbolKind = undefined;
                return false;
            }
            name = matches[1];
            const spaces = matches[2];
            const rest = matches[3];
            if (name === '') {
                charIdx += COMMA_LEN;
                continue;
            }

            // Given a constant operator like Foo(_, _, ...), match the parentheses and everything inside of it
            const isConstantOperator = /^(\(((\s*_\s*,|\s*_\s*)\s*)+\))$/.test(rest);

            if (rest !== '' && !isCommentStart(rest) &&!isConstantOperator) {
                module.simpleListSymbolKind = undefined;
                return false;
            }
            module.addSymbol(new vscode.SymbolInformation(
                name,
                module.simpleListSymbolKind,
                module.containerName,
                new vscode.Location(docUri, new vscode.Position(lineNum, charIdx))
            ));
            charIdx += name.length + spaces.length + COMMA_LEN;
            if (isConstantOperator) {
                // Skip '(...)' in constant operators e.g. Foo(_, _)
                charIdx += rest.length;
            }
            if (rest !== '' && !isConstantOperator) {
                module.simpleListSymbolKind = undefined;
                break;      // There were no comma after the name
            }
        }
        if (name !== '') {
            module.simpleListSymbolKind = undefined;   // There were no comma after the last name
        }
        return true;
    }

    tryExtractTheoremAxiomLemma(
        module: ModuleContext,
        docUri: vscode.Uri,
        line: vscode.TextLine
    ): boolean {
        const matches = /^\s*(?:THEOREM|AXIOM|LEMMA)\s*(\w+)\s*==/g.exec(line.text);
        if (!matches) {
            return false;
        }
        module.addSymbol(new vscode.SymbolInformation(
            matches[1],
            vscode.SymbolKind.Boolean,
            module.containerName,
            new vscode.Location(docUri, line.range.start)
        ));
        return true;
    }

    tryStartPlusCal(
        context: ParsingContext,
        docUri: vscode.Uri,
        line: vscode.TextLine
    ): boolean {
        const matches = /(\(\*.*)--((?:fair\s+)?algorithm)\b\s*/g.exec(line.text);
        if (!matches) {
            return false;
        }
        const algName = line.text.substring(matches[0].length) || PLUS_CAL_DEFAULT_NAME;
        const symbol = new vscode.SymbolInformation(
            algName,
            vscode.SymbolKind.Namespace,
            ROOT_CONTAINER_NAME,
            new vscode.Location(docUri, line.range.start)
        );
        context.startPlusCal(symbol);
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
function findBlockDefinitionEnd(
    document: vscode.TextDocument,
    startLine: vscode.TextLine,
    indent: number
): vscode.TextLine {
    let lastLine = startLine;
    for (let i = startLine.lineNumber + 1; i < document.lineCount; i++) {
        const line = document.lineAt(i);
        if (line.isEmptyOrWhitespace) {
            continue;
        }
        if (line.firstNonWhitespaceCharacterIndex <= indent) {      // New block started
            break;
        }
        lastLine = line;
    }
    return lastLine;
}
