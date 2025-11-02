import * as vscode from 'vscode';
import * as path from 'path';
import { TlaDocumentInfos, TlaDocumentInfo } from '../model/documentInfo';
import { moduleSearchPaths } from '../paths';
function createJarUri(archivePath: string, internalPath: string): vscode.Uri {
    const normalizedInternal = internalPath.startsWith('/')
        ? internalPath
        : `/${internalPath}`;
    return vscode.Uri.parse(`jarfile:${archivePath}!${normalizedInternal}`);
}

/**
 * Check if line is a statement boundary
 */
function isStatementBoundary(
    line: string,
    allowInstance: boolean = false,
): boolean {
    if (/^={4,}/.test(line) || /^-{4,}/.test(line)) {
        return true;
    }
    if (
        /\b==\b/.test(line) &&
    (!allowInstance || !/\bINSTANCE\b/.test(line))
    ) {
        return true;
    }
    return false;
}

/**
 * Check if the position is within an EXTENDS or INSTANCE clause and return the module name if so
 */
function getModuleReference(
    document: vscode.TextDocument,
    position: vscode.Position,
): string | undefined {
    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return undefined;
    }

    const word = document.getText(range);
    if (!getModuleClauseContext(document, range)) {
        return undefined;
    }

    return word;
}

type ModuleClause = 'EXTENDS' | 'INSTANCE';

interface InstanceWithContext {
  moduleName: string;
  symbolName: string;
}

function getModuleClauseContext(
    document: vscode.TextDocument,
    range: vscode.Range,
): ModuleClause | undefined {
    const statementStart = findStatementStartLine(document, range.start.line);
    const fragmentRange = new vscode.Range(
        new vscode.Position(statementStart, 0),
        range.start,
    );
    const fragmentText = document.getText(fragmentRange);

    const extendsIndex = fragmentText.lastIndexOf('EXTENDS');
    const instanceIndex = fragmentText.lastIndexOf('INSTANCE');

    if (extendsIndex < 0 && instanceIndex < 0) {
        return undefined;
    }

    if (extendsIndex > instanceIndex) {
        const afterExtends = fragmentText.substring(
            extendsIndex + 'EXTENDS'.length,
        );
        if (containsTerminator(afterExtends)) {
            return undefined;
        }
        return 'EXTENDS';
    }

    const afterInstance = fragmentText.substring(
        instanceIndex + 'INSTANCE'.length,
    );
    if (/\bWITH\b/.test(afterInstance) || containsTerminator(afterInstance)) {
        return undefined;
    }
    return 'INSTANCE';
}

function findStatementStartLine(
    document: vscode.TextDocument,
    line: number,
): number {
    for (let lineNum = line; lineNum > 0; lineNum--) {
        const prevLine = document.lineAt(lineNum - 1).text;
        if (isStatementBoundary(prevLine, true)) {
            return lineNum;
        }
    }
    return 0;
}

function containsTerminator(fragment: string): boolean {
    return /\bWITH\b|\bLET\b|\b==\b|\bINSTANCE\b/.test(fragment);
}

function findStatementEndLine(
    document: vscode.TextDocument,
    line: number,
): number {
    let endLine = line;
    for (let lineNum = line; lineNum < document.lineCount - 1; lineNum++) {
        const nextLine = document.lineAt(lineNum + 1).text;
        if (isStatementBoundary(nextLine, true)) {
            break;
        }
        endLine = lineNum + 1;
    }
    return endLine;
}

function getStatementRange(
    document: vscode.TextDocument,
    position: vscode.Position,
): vscode.Range {
    const startLine = findStatementStartLine(document, position.line);
    const endLine = findStatementEndLine(document, position.line);
    const endRange = document.lineAt(endLine).range.end;
    return new vscode.Range(new vscode.Position(startLine, 0), endRange);
}

function getInstanceWithContext(
    document: vscode.TextDocument,
    position: vscode.Position,
): InstanceWithContext | undefined {
    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return undefined;
    }

    const statementRange = getStatementRange(document, range.start);
    const statementText = document.getText(statementRange);
    const wordOffset =
    document.offsetAt(range.start) - document.offsetAt(statementRange.start);

    const beforeWord = statementText.substring(0, wordOffset);
    const instanceMatches = Array.from(
        beforeWord.matchAll(/INSTANCE\s+([A-Za-z0-9_']+)/g),
    );
    if (instanceMatches.length === 0) {
        return undefined;
    }

    const lastInstanceMatch = instanceMatches[instanceMatches.length - 1];
    const moduleName = lastInstanceMatch[1];
    const instanceIndex = lastInstanceMatch.index ?? -1;

    const withIndex = beforeWord.toUpperCase().lastIndexOf('WITH');
    if (withIndex < 0 || withIndex < instanceIndex) {
        return undefined;
    }

    if (!isLeftHandSideOfInstanceAssignment(statementText, wordOffset)) {
        return undefined;
    }

    return {
        moduleName,
        symbolName: document.getText(range),
    };
}

function stripComments(text: string): string {
    return text
        .replace(/\(\*[\s\S]*?\*\)/g, ' ')
        .replace(/\\\*.*$/gm, '');
}

function extractModuleNamesFromStatement(
    statementText: string,
    keyword: 'EXTENDS' | 'INSTANCE',
): string[] {
    const normalized = stripComments(statementText);
    const keywordIndex = normalized
        .toUpperCase()
        .indexOf(keyword.toUpperCase());
    if (keywordIndex < 0) {
        return [];
    }

    let after = normalized.substring(keywordIndex + keyword.length);
    if (keyword === 'INSTANCE') {
        const withIndex = after.toUpperCase().indexOf('WITH');
        if (withIndex >= 0) {
            after = after.substring(0, withIndex);
        }
    }

    return after
        .split(',')
        .map((part) => part.trim())
        .map((part) => {
            const match = /^([A-Za-z0-9_']+)/.exec(part);
            return match ? match[1] : undefined;
        })
        .filter((name): name is string => !!name);
}

function collectReferencedModules(
    document: vscode.TextDocument,
): string[] {
    const documentText = document.getText();
    const seenStatements = new Set<string>();
    const modules = new Set<string>();

    const processKeyword = (keyword: 'EXTENDS' | 'INSTANCE') => {
        const regex = new RegExp(`\\b${keyword}\\b`, 'gi');
        let match: RegExpExecArray | null;
        while ((match = regex.exec(documentText))) {
            const position = document.positionAt(match.index);
            const statementRange = getStatementRange(document, position);
            const key = `${statementRange.start.line}:${statementRange.start.character}`;
            if (seenStatements.has(`${keyword}:${key}`)) {
                continue;
            }
            seenStatements.add(`${keyword}:${key}`);
            const statementText = document.getText(statementRange);
            const names = extractModuleNamesFromStatement(statementText, keyword);
            for (const name of names) {
                modules.add(name);
            }
        }
    };

    processKeyword('EXTENDS');
    processKeyword('INSTANCE');

    return Array.from(modules);
}

function isLeftHandSideOfInstanceAssignment(
    statementText: string,
    wordOffset: number,
): boolean {
    for (let index = wordOffset - 1; index >= 0; index--) {
        const ch = statementText[index];
        if (/\s/.test(ch)) {
            continue;
        }
        if (ch === ',') {
            return true;
        }
        if (ch === '-') {
            if (index > 0 && statementText[index - 1] === '<') {
                return false;
            }
        }
        if (
            (ch === 'H' || ch === 'h') &&
      index >= 3 &&
      statementText.substring(index - 3, index + 1).toUpperCase() === 'WITH'
        ) {
            return true;
        }
    }
    return false;
}

/**
 * Try to find a TLA+ module file given a module name
 */
async function findModuleFile(
    moduleName: string,
    currentDocumentUri: vscode.Uri,
): Promise<vscode.Uri | undefined> {
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
        `**/lib/${moduleFileName}`,
    ];

    for (const pattern of searchPatterns) {
        const foundFiles = await vscode.workspace.findFiles(pattern, undefined, 1);
        if (foundFiles.length > 0) {
            return foundFiles[0];
        }
    }

    const resolved = await findModuleInSearchPaths(
        moduleFileName,
        currentDocumentUri,
    );
    if (resolved) {
        return resolved;
    }

    return undefined;
}

async function findModuleInSearchPaths(
    moduleFileName: string,
    currentDocumentUri: vscode.Uri,
): Promise<vscode.Uri | undefined> {
    const sources = moduleSearchPaths.getSources();
    for (const source of sources) {
        const basePaths = moduleSearchPaths.getSourcePaths(source.name) ?? [];
        for (const basePath of basePaths) {
            const candidate = await resolveModuleInBasePath(
                basePath,
                moduleFileName,
                currentDocumentUri,
            );
            if (candidate) {
                return candidate;
            }
        }
    }
    return undefined;
}

async function resolveModuleInBasePath(
    basePath: string,
    moduleFileName: string,
    currentDocumentUri: vscode.Uri,
): Promise<vscode.Uri | undefined> {
    if (!basePath) {
        return undefined;
    }

    try {
        if (basePath.startsWith('jar:file:') || basePath.startsWith('jarfile:')) {
            const exclamationIndex = basePath.indexOf('!');
            if (exclamationIndex < 0) {
                return undefined;
            }

            const innerPath = basePath.substring(exclamationIndex + 1);
            const normalizedInner = innerPath.startsWith('/')
                ? innerPath
                : `/${innerPath}`;
            const entryRoot = normalizedInner.replace(/^\//, '');
            const moduleInnerPath = path.posix.join(entryRoot, moduleFileName);

            let jarFsPath: string | undefined;
            if (basePath.startsWith('jar:file:')) {
                const jarPrefix = basePath.substring(0, exclamationIndex);
                const jarFileUri = vscode.Uri.parse(jarPrefix.replace(/^jar:/, ''));
                jarFsPath = jarFileUri.fsPath;
            } else {
                const rawPath = basePath.substring('jarfile:'.length, exclamationIndex);
                try {
                    jarFsPath = vscode.Uri.file(rawPath).fsPath;
                } catch {
                    jarFsPath = rawPath;
                }
            }

            if (!jarFsPath) {
                return undefined;
            }

            const jarUri = createJarUri(jarFsPath, moduleInnerPath);
            try {
                await vscode.workspace.fs.stat(jarUri);
                return jarUri;
            } catch {
                return undefined;
            }
        }

        const workspaceFolder = vscode.workspace.getWorkspaceFolder(
            currentDocumentUri,
        );
        const baseDir = workspaceFolder
            ? workspaceFolder.uri.fsPath
            : path.dirname(currentDocumentUri.fsPath);
        const modulePath = path.isAbsolute(basePath)
            ? path.join(basePath, moduleFileName)
            : path.join(baseDir, basePath, moduleFileName);
        const candidate = vscode.Uri.file(modulePath);
        await vscode.workspace.fs.stat(candidate);
        return candidate;
    } catch {
    // Ignore directories that do not contain the module
    }
    return undefined;
}

async function ensureModuleSymbols(
    moduleUri: vscode.Uri,
    docInfos: TlaDocumentInfos,
): Promise<void> {
    if (moduleUri.scheme !== 'file') {
        return;
    }
    const cached = docInfos.get(moduleUri);
    if (cached.symbols.length > 0 || cached.plusCalSymbols.length > 0) {
        return;
    }

    try {
        await vscode.workspace.openTextDocument(moduleUri);
    } catch {
        return;
    }

    try {
        await vscode.commands.executeCommand(
            'vscode.executeDocumentSymbolProvider',
            moduleUri,
        );
    } catch {
    // ignore symbol provider failures; fallback will handle navigation
    }
}

async function findSymbolInModule(
    moduleUri: vscode.Uri,
    symbolName: string,
    docInfos: TlaDocumentInfos,
): Promise<vscode.Location | undefined> {
    await ensureModuleSymbols(moduleUri, docInfos);
    const document = await vscode.workspace.openTextDocument(moduleUri);
    const searchName = trimTicks(symbolName);
    const escapedName = searchName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const definitionPattern = new RegExp(
        `^(\\s*)(${escapedName})(\\b|\\(|\\[|')`,
        'm',
    );

    const text = document.getText();
    const match = definitionPattern.exec(text);
    if (!match) {
        return undefined;
    }

    const leadingWhitespace = match[1] ?? '';
    const symbolSegment = match[2] ?? searchName;
    const symbolOffset = match.index + leadingWhitespace.length;
    const position = document.positionAt(symbolOffset);
    const endPosition = position.translate(0, symbolSegment.length);
    return new vscode.Location(moduleUri, new vscode.Range(position, endPosition));
}

/**
 * Check if position is a record field access (e.g., state.x)
 */
function isRecordFieldAccess(line: string, range: vscode.Range): boolean {
    if (
        range.start.character > 0 &&
    line.charAt(range.start.character - 1) === '.'
    ) {
        return true;
    }
    // Check for EXCEPT expression field access (e.g., [state EXCEPT !.x = ...])
    if (
        range.start.character > 1 &&
    line.substring(range.start.character - 2, range.start.character) === '!.'
    ) {
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
function isInRecordDefinition(
    document: vscode.TextDocument,
    line: string,
    range: vscode.Range,
): boolean {
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
function symbolLocations(
    document: vscode.TextDocument,
    docInfo: TlaDocumentInfo,
    position: vscode.Position,
) {
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
        if (
            symbol.name === word &&
      symbol.location.range.start.isBeforeOrEqual(range.start)
        ) {
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
    docInfos: TlaDocumentInfos,
): Promise<vscode.Location | vscode.Location[] | undefined> {
    // First check if we're inside an INSTANCE ... WITH clause (left-hand side)
    const instanceContext = getInstanceWithContext(document, position);
    if (instanceContext) {
        const moduleUri = await findModuleFile(instanceContext.moduleName, document.uri);
        if (moduleUri) {
            const targetLocation = await findSymbolInModule(
                moduleUri,
                instanceContext.symbolName,
                docInfos,
            );
            if (targetLocation) {
                return targetLocation;
            }
            // Fallback to the module start if symbol lookup failed
            return new vscode.Location(moduleUri, new vscode.Position(0, 0));
        }
    }

    // Then check if we're in an EXTENDS or INSTANCE clause
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
    const localLocations = docInfo
        ? symbolLocations(document, docInfo, position) ?? []
        : [];

    if (localLocations.length > 0) {
        return localLocations;
    }

    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return localLocations;
    }

    const searchName = trimTicks(document.getText(range));
    if (!searchName) {
        return localLocations;
    }

    const referencedModules = collectReferencedModules(document);
    for (const moduleName of referencedModules) {
        const moduleUri = await findModuleFile(moduleName, document.uri);
        if (!moduleUri) {
            continue;
        }
        const targetLocation = await findSymbolInModule(
            moduleUri,
            searchName,
            docInfos,
        );
        if (targetLocation) {
            return targetLocation;
        }
    }

    return localLocations;
}

export class TlaDeclarationsProvider implements vscode.DeclarationProvider {
    constructor(private readonly docInfos: TlaDocumentInfos) {}

    provideDeclaration(
        document: vscode.TextDocument,
        position: vscode.Position,
        _token: vscode.CancellationToken,
    ): vscode.ProviderResult<vscode.Declaration> {
        return provideSymbolLocations(document, position, this.docInfos);
    }
}

export class TlaDefinitionsProvider implements vscode.DefinitionProvider {
    constructor(private readonly docInfos: TlaDocumentInfos) {}

    provideDefinition(
        document: vscode.TextDocument,
        position: vscode.Position,
        _token: vscode.CancellationToken,
    ): vscode.ProviderResult<vscode.Declaration> {
        return provideSymbolLocations(document, position, this.docInfos);
    }
}

function trimTicks(str: string): string {
    const tickIdx = str.indexOf("'");
    return tickIdx < 0 ? str : str.substring(0, tickIdx);
}
