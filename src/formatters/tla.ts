import * as vscode from 'vscode';
import { IndentationType, LineInfo, makeSpaces, indentRight, indentExact, indentationLen } from './formatting';

/**
 * Formats the code on the fly in .tla files.
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
                        || findEnclosingBlockStart(document, position.line - 1);
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
    const startInfo = findEnclosingBlockStart(document, position.line - 1);
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

/**
 * Finds the beginning of the block that encloses the given line.
 */
function findEnclosingBlockStart(document: vscode.TextDocument, lineNo: number): LineInfo | undefined {
    let n = lineNo;
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
    const gMatches = /^(\s*)(?:variables|VARIABLE(S)?|CONSTANT(S)?|\w+:)\s*$/g.exec(line.text);
    return gMatches ? new LineInfo(line, gMatches[1], IndentationType.Right) : undefined;
}

function testStateDefBlockStart(line: vscode.TextLine, options: vscode.FormattingOptions): LineInfo | undefined {
    const gMatches = /^((\s*)[\w(),\s]+==\s*)((?:\/\\|\\\/).*)?\s*$/g.exec(line.text);
    if (!gMatches) {
        return undefined;
    }
    if (gMatches[3]) {
        return new LineInfo(line, makeSpaces(indentationLen(gMatches[1], options)), IndentationType.Exact);
    }
    return new LineInfo(line, gMatches[2], IndentationType.Right);
}

function testBlockStart(line: vscode.TextLine): LineInfo | undefined {
    // eslint-disable-next-line max-len
    const matches = /^(\s*)(?:\w+:)?\s*(?:begin\b|if\b|else\b|elsif\b|while\b|either\b|or\b|with\b|define\b|macro\b|procedure\b|\{).*/g.exec(line.text);
    return matches ? new LineInfo(line, matches[1], IndentationType.Right) : undefined;
}

function testBlockEnd(line: vscode.TextLine): LineInfo | undefined {
    const matches = /^(\s*)(?:end\b|else\b|elsif\b|or\b|\}).*/g.exec(line.text);
    return matches ? new LineInfo(line, matches[1], IndentationType.Left) : undefined;
}
