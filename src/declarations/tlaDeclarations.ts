import * as vscode from 'vscode';
import { TlaDocumentInfos, TlaDocumentInfo } from '../model/documentInfo';

function symbolLocations(document: vscode.TextDocument, docInfo: TlaDocumentInfo, position: vscode.Position) {
    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return undefined;
    }

    // Check if the word is preceded by a dot, which would indicate it's a record field access
    const line = document.lineAt(position.line).text;
    if (range.start.character > 0 && line.charAt(range.start.character - 1) === '.') {
        // This is a record field access (e.g., state.x), not a symbol reference
        return undefined;
    }

    // Check if the word is preceded by "!." which would indicate it's in an EXCEPT expression
    if (range.start.character > 1 && line.substring(range.start.character - 2, range.start.character) === '!.') {
        // This is a record field in EXCEPT expression (e.g., [state EXCEPT !.x = ...])
        return undefined;
    }

    // Check if this is a field name in a record definition (e.g., [bar |-> value])
    // First check if we have |-> after the word on the same line
    const afterWord = line.substring(range.end.character);
    if (/^\s*\|->/.test(afterWord)) {
        // Now check if we're inside a record definition by looking backwards
        // for an unmatched opening bracket [
        let bracketDepth = 0;
        let foundRecordStart = false;

        // Check current line before the word
        const beforeWord = line.substring(0, range.start.character);
        for (let i = beforeWord.length - 1; i >= 0; i--) {
            if (beforeWord[i] === ']') {bracketDepth++;}
            else if (beforeWord[i] === '[') {
                bracketDepth--;
                if (bracketDepth < 0) {
                    foundRecordStart = true;
                    break;
                }
            }
        }

        // If not found on current line, check previous lines
        if (!foundRecordStart && position.line > 0) {
            for (let lineNum = position.line - 1; lineNum >= 0 && !foundRecordStart; lineNum--) {
                const prevLine = document.lineAt(lineNum).text;
                for (let i = prevLine.length - 1; i >= 0; i--) {
                    if (prevLine[i] === ']') {bracketDepth++;}
                    else if (prevLine[i] === '[') {
                        bracketDepth--;
                        if (bracketDepth < 0) {
                            foundRecordStart = true;
                            break;
                        }
                    }
                }
            }
        }

        if (foundRecordStart) {
            // This is a record field definition, not a symbol reference
            return undefined;
        }
    }

    const rawWord = line.substring(range.start.character, range.end.character);
    const word = trimTicks(rawWord);
    const symbols = docInfo.isPlusCalAt(position)
        ? docInfo.symbols.concat(docInfo.plusCalSymbols)
        : docInfo.symbols;
    const locations = [];
    for (const symbol of symbols) {
        if (symbol.name === word && symbol.location.range.start.isBeforeOrEqual(range.start)) {
            locations.push(symbol.location);
        }
    }
    return locations;
}

export class TlaDeclarationsProvider implements vscode.DeclarationProvider {
    constructor(
        private readonly docInfos: TlaDocumentInfos
    ) { }

    provideDeclaration(
        document: vscode.TextDocument,
        position: vscode.Position,
        _token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.Declaration> {
        const docInfo = this.docInfos.get(document.uri);
        return docInfo ? symbolLocations(document, docInfo, position) || [] : undefined;
    }
}

export class TlaDefinitionsProvider implements vscode.DefinitionProvider {
    constructor(
        private readonly docInfos: TlaDocumentInfos
    ) { }

    provideDefinition(
        document: vscode.TextDocument,
        position: vscode.Position,
        _token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.Declaration> {
        const docInfo = this.docInfos.get(document.uri);
        return docInfo ? symbolLocations(document, docInfo, position) || [] : undefined;
    }
}

function trimTicks(str: string): string {
    const tickIdx = str.indexOf("'");
    return tickIdx < 0 ? str : str.substring(0, tickIdx);
}
