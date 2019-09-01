import * as vscode from 'vscode';
import { start } from 'repl';

const SPACES = ['', ' ', '  ', '   ', '    '];

enum IndentationType {
    Exact,
    Right,
    Left
}

class LineInfo {
    constructor(
        readonly line: vscode.TextLine,
        readonly indentation: string,
        readonly indentationType: IndentationType
    ) {}
}

/**
 * Formats the code on the fly.
 */
export class TlaOnTypeFormattingEditProvider implements vscode.OnTypeFormattingEditProvider {
    provideOnTypeFormattingEdits(
        document: vscode.TextDocument,
        position: vscode.Position,
        ch: string,
        options: vscode.FormattingOptions,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.TextEdit[]> {
        if (position.line === 0) {
            return [];
        }
        // VSCode does the simple formatting itself (keeps indentation from the previous line)
        // So, we only need to correct it when necessary
        if (ch === '\n') {
            return tryIndentBlockStart(document, position, options);
        } else if (ch === 'd' || ch === 'e' || ch === 'f' || ch === 'r') {
            return tryIndentBlockEnd(document, position, options);
        }
        return [];
    }
}

/**
 * Indents text inside a block.
 */
function tryIndentBlockStart(
    document: vscode.TextDocument,
    position: vscode.Position,
    options: vscode.FormattingOptions
): vscode.TextEdit[] {
    const prevLine = document.lineAt(position.line - 1);
    const startInfo = testSimpleBlockStart(prevLine)
                        || testStateDefBlockStart(prevLine, options)
                        || findOuterBlockStart(document, position.line - 1);
    if (!startInfo) {
        return [];
    }
    const lineText = document.lineAt(position.line).text;
    switch (startInfo.indentationType) {
        case IndentationType.Right:
            return indentRight(lineText, position, startInfo.indentation, options);
        case IndentationType.Exact:
            return indentExact(lineText, position, startInfo.indentation);
    }
    return [];
}

/**
 * Indents a line that ends some block by aligning it to the block start.
 */
function tryIndentBlockEnd(
    document: vscode.TextDocument,
    position: vscode.Position,
    options: vscode.FormattingOptions
): vscode.TextEdit[] {
    const line = document.lineAt(position.line);
    const endInfo = testBlockEnd(line);
    if (!endInfo || endInfo.indentation.length === 0) {
        return [];
    }
    const startInfo = findOuterBlockStart(document, position.line - 1);
    if (!startInfo) {
        return [];
    }
    const startIndentLen = indentationLen(startInfo.indentation, options);
    const endIndentLen = indentationLen(endInfo.indentation, options);
    if (endIndentLen === startIndentLen) {
        return [];
    }
    const lineStart = new vscode.Position(position.line, 0);
    const indentationEnd = new vscode.Position(position.line, endIndentLen);
    return [
        vscode.TextEdit.replace(new vscode.Range(lineStart, indentationEnd), startInfo.indentation)
    ];
}

function findOuterBlockStart(
    document: vscode.TextDocument,
    start: number
): LineInfo | undefined {
    let n = start;
    while (n >= 0) {
        const line = document.lineAt(n);
        const startInfo = testBlockStart(line);
        if (startInfo) {
            return startInfo;
        }
        const endInfo = testBlockEnd(line);
        if (endInfo) {
            return undefined;
        }
        if (line.text.length > 0 && !line.text.startsWith(' ') && !line.text.startsWith('\n')) {
            return undefined;  // some text with no indentation, stop analysis to prevent too long searching
        }
        n -= 1;
    }
    return undefined;
}

function testSimpleBlockStart(line: vscode.TextLine): LineInfo | undefined {
    const gMatches = /^(\s*)(?:variables|VARIABLES|CONSTANTS|\w+:)\s*$/g.exec(line.text);
    return gMatches ? new LineInfo(line, gMatches[1], IndentationType.Right) : undefined;
}

function testStateDefBlockStart(line: vscode.TextLine, options: vscode.FormattingOptions): LineInfo | undefined {
    const gMatches = /^((\s*)\w+\s*==\s*)((?:\/\\|\\\/).*)?\s*$/g.exec(line.text);
    if (!gMatches) {
        return undefined;
    }
    if (gMatches[3]) {
        return new LineInfo(line, spaces(indentationLen(gMatches[1], options)), IndentationType.Exact);
    }
    return new LineInfo(line, gMatches[2], IndentationType.Right);
}

function testBlockStart(line: vscode.TextLine): LineInfo | undefined {
    const matches = /^(\s*)(?:\w+\:)?\s*(?:begin|if|else|elsif|while|either|or|with|define|macro|procedure)\b.*/g.exec(line.text);
    return matches ? new LineInfo(line, matches[1], IndentationType.Right) : undefined;
}

function testBlockEnd(line: vscode.TextLine): LineInfo | undefined {
    const matches = /^(\s*)(?:end|else|elsif|or)\b.*/g.exec(line.text);
    return matches ? new LineInfo(line, matches[1], IndentationType.Left) : undefined;
}

function indentRight(
    lineText: string,
    position: vscode.Position,
    baseIndentation: string,
    options: vscode.FormattingOptions
) {
    if (lineText === baseIndentation) {
        // The user has just hit the Enter right after the block start
        // and VSCode aligned the new line to the block start. Just add a new tab.
        return [ vscode.TextEdit.insert(position, makeTab(options)) ];
    }
    if (position.character === indentationLen(baseIndentation, options) + options.tabSize) {
        // The user just hit the Enter while continuing to type inside already indented
        // block. VSCode does everyting itself.
        return [];
    }
    // Otherwise just force the correct indentation
    // This works in all cases. The cases above are just to improve user experience a bit
    const newIdent = baseIndentation + makeTab(options);
    const lineStart = new vscode.Position(position.line, 0);
    return [ vscode.TextEdit.replace(new vscode.Range(lineStart, position), newIdent) ];
}

function indentExact(
    lineText: string,
    position: vscode.Position,
    indentation: string
) {
    if (lineText === indentation) {
        return [];
    }
    const lineStart = new vscode.Position(position.line, 0);
    return [ vscode.TextEdit.replace(new vscode.Range(lineStart, position), indentation) ];
}

function makeTab(options: vscode.FormattingOptions): string {
    if (!options.insertSpaces) {
        return '\t';
    }
    return spaces(options.tabSize);
}

function indentationLen(str: string, options: vscode.FormattingOptions): number {
    let len = 0;
    for (const ch of str) {
        if (ch === '\t') {
            len += options.tabSize;
        } else {
            len += 1;
        }
    }
    return len;
}

function spaces(num: number) {
    if (num < SPACES.length) {
        return SPACES[num];
    }
    let len = SPACES.length - 1;
    const spaces = SPACES.slice(SPACES.length - 1);
    while (len < num) {
        len += 1;
        spaces.push(' ');
    }
    return spaces.join('');
}
