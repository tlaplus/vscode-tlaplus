import * as vscode from 'vscode';
import * as path from 'path';
import { TlaDocumentInfos, TlaDocumentInfo } from '../model/documentInfo';

/**
 * Check if text contains EXTENDS keyword
 */
function hasExtendsKeyword(text: string): boolean {
    return /\bEXTENDS\b/.test(text);
}

/**
 * Check if text contains INSTANCE keyword
 */
function hasInstanceKeyword(text: string): boolean {
    return /\bINSTANCE\b/.test(text);
}

/**
 * Check if line is a statement boundary
 */
function isStatementBoundary(line: string, allowInstance: boolean = false): boolean {
    if (/^={4,}/.test(line) || /^-{4,}/.test(line)) {
        return true;
    }
    if (/==\s*$/.test(line) && (!allowInstance || !line.includes('INSTANCE'))) {
        return true;
    }
    return false;
}

/**
 * Check current line for module reference keywords
 */
function checkCurrentLine(beforeWord: string): boolean {
    return hasExtendsKeyword(beforeWord) ||
        hasInstanceKeyword(beforeWord) ||
        /==\s*INSTANCE\s*$/.test(beforeWord);
}

/**
 * Search previous lines for module reference keywords
 */
function searchPreviousLines(document: vscode.TextDocument, position: vscode.Position): boolean {
    for (let lineNum = position.line - 1; lineNum >= 0; lineNum--) {
        const prevLine = document.lineAt(lineNum).text;

        if (isStatementBoundary(prevLine, true)) {
            break;
        }

        if (hasExtendsKeyword(prevLine) || hasInstanceKeyword(prevLine)) {
            return true;
        }
    }
    return false;
}

/**
 * Search following lines for EXTENDS in multi-line declarations
 */
function searchFollowingLines(document: vscode.TextDocument, position: vscode.Position, afterWord: string): boolean {
    if (position.line >= document.lineCount - 1) {
        return false;
    }

    for (let lineNum = position.line + 1; lineNum < document.lineCount; lineNum++) {
        const nextLine = document.lineAt(lineNum).text;

        if (isStatementBoundary(nextLine, true)) {
            break;
        }

        // Check if there's a comma after our word (for EXTENDS lists)
        if (lineNum === position.line + 1 && /^\s*,/.test(afterWord)) {
            if (hasExtendsKeyword(nextLine)) {
                return true;
            }
        }
    }
    return false;
}

/**
 * Check if the position is within an EXTENDS or INSTANCE clause and return the module name if so
 */
function getModuleReference(document: vscode.TextDocument, position: vscode.Position): string | undefined {
    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return undefined;
    }

    const line = document.lineAt(position.line).text;
    const word = document.getText(range);
    const beforeWord = line.substring(0, range.start.character);

    // Check current line
    if (checkCurrentLine(beforeWord)) {
        return word;
    }

    // Check previous lines
    if (position.line > 0 && searchPreviousLines(document, position)) {
        return word;
    }

    // Check following lines for multi-line EXTENDS
    const afterWord = line.substring(range.end.character);
    if (searchFollowingLines(document, position, afterWord)) {
        return word;
    }

    return undefined;
}

/**
 * Try to find a TLA+ module file given a module name
 */
async function findModuleFile(moduleName: string, currentDocumentUri: vscode.Uri): Promise<vscode.Uri | undefined> {
    // Standard library modules that don't have physical files
    const standardModules = [
        'TLC', 'Integers', 'Naturals', 'Reals', 'Sequences', 'FiniteSets',
        'Bags', 'RealTime', 'TLCExt', 'Json', 'IOUtils', 'SVG', 'Bitwise',
        'FiniteSetsExt', 'Functions', 'CSV', 'Combinatorics', 'Folds',
        'Graphs', 'SequencesExt', 'BagsExt', 'DifferentialEquations',
        'VectorClocks'
    ];

    if (standardModules.includes(moduleName)) {
        // These are standard library modules, no file to navigate to
        return undefined;
    }

    const moduleFileName = `${moduleName}.tla`;

    // First, try to find the module file in the same directory as the current document
    const currentDir = path.dirname(currentDocumentUri.fsPath);
    const modulePath = path.join(currentDir, moduleFileName);
    const moduleUri = vscode.Uri.file(modulePath);

    try {
        await vscode.workspace.fs.stat(moduleUri);
        return moduleUri;
    } catch {
        // File doesn't exist in current directory, continue searching
    }

    const searchPatterns = [
        `**/${moduleFileName}`,
        `**/modules/${moduleFileName}`,
        `**/specs/${moduleFileName}`,
        `**/src/${moduleFileName}`,
        `**/lib/${moduleFileName}`
    ];

    for (const pattern of searchPatterns) {
        const foundFiles = await vscode.workspace.findFiles(pattern, undefined, 1);
        if (foundFiles.length > 0) {
            return foundFiles[0];
        }
    }

    return undefined;
}

/**
 * Check if position is a record field access (e.g., state.x)
 */
function isRecordFieldAccess(line: string, range: vscode.Range): boolean {
    if (range.start.character > 0 && line.charAt(range.start.character - 1) === '.') {
        return true;
    }
    // Check for EXCEPT expression field access (e.g., [state EXCEPT !.x = ...])
    if (range.start.character > 1 && line.substring(range.start.character - 2, range.start.character) === '!.') {
        return true;
    }
    return false;
}

/**
 * Count bracket depth in a string
 */
function updateBracketDepth(text: string, startDepth: number = 0): number {
    let depth = startDepth;
    for (let i = text.length - 1; i >= 0; i--) {
        if (text[i] === ']') {
            depth++;
        } else if (text[i] === '[') {
            depth--;
            if (depth < 0) {
                return -1; // Found unmatched opening bracket
            }
        }
    }
    return depth;
}

/**
 * Check if position is inside a record field definition
 */
function isInRecordDefinition(document: vscode.TextDocument, line: string, range: vscode.Range): boolean {
    const afterWord = line.substring(range.end.character);
    if (!/^\s*\|->/.test(afterWord)) {
        return false;
    }

    // Check current line before the word
    const beforeWord = line.substring(0, range.start.character);
    if (updateBracketDepth(beforeWord) === -1) {
        return true;
    }

    // Check previous lines
    if (range.start.line > 0) {
        let bracketDepth = updateBracketDepth(beforeWord);
        for (let lineNum = range.start.line - 1; lineNum >= 0; lineNum--) {
            const prevLine = document.lineAt(lineNum).text;
            bracketDepth = updateBracketDepth(prevLine, bracketDepth);
            if (bracketDepth === -1) {
                return true;
            }
        }
    }

    return false;
}

/**
 * Find symbol locations in the document
 */
function symbolLocations(document: vscode.TextDocument, docInfo: TlaDocumentInfo, position: vscode.Position) {
    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return undefined;
    }

    const line = document.lineAt(position.line).text;

    // Check if this is a record field access
    if (isRecordFieldAccess(line, range)) {
        return undefined;
    }

    // Check if this is a field name in a record definition
    if (isInRecordDefinition(document, line, range)) {
        return undefined;
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

/**
 * Common logic for providing declarations/definitions
 */
async function provideSymbolLocations(
    document: vscode.TextDocument,
    position: vscode.Position,
    docInfos: TlaDocumentInfos
): Promise<vscode.Location | vscode.Location[] | undefined> {
    // First check if we're in an EXTENDS or INSTANCE clause
    const moduleRef = getModuleReference(document, position);

    if (moduleRef) {
        const moduleUri = await findModuleFile(moduleRef, document.uri);
        if (moduleUri) {
            // Return location at the beginning of the module file
            return new vscode.Location(moduleUri, new vscode.Position(0, 0));
        }
    }

    // Fall back to regular symbol resolution
    const docInfo = docInfos.get(document.uri);
    return docInfo ? symbolLocations(document, docInfo, position) || [] : undefined;
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
        return provideSymbolLocations(document, position, this.docInfos);
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
        return provideSymbolLocations(document, position, this.docInfos);
    }
}

function trimTicks(str: string): string {
    const tickIdx = str.indexOf("'");
    return tickIdx < 0 ? str : str.substring(0, tickIdx);
}