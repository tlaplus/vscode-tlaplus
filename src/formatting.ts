import * as vscode from 'vscode';
import { start } from 'repl';

const SPACES = ['', ' ', '  ', '   ', '    '];

class LineInfo {
    constructor(
        readonly line: vscode.TextLine,
        readonly indentation: string
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
    const startInfo = findOuterBlockStart(document, position.line - 1);
    if (!startInfo) {
        return [];
    }
    const lineText = document.lineAt(position.line).text;
    if (lineText === startInfo.indentation) {
        // The user has just hit the Enter right after the block start
        // and VSCode aligned the new line to the block start. Just add a new tab.
        return [ vscode.TextEdit.insert(position, makeTab(options)) ];
    }
    if (position.character === indentationLen(startInfo.indentation, options) + options.tabSize) {
        // The user just hit the Enter while continuing to type inside already indented
        // block. VSCode does everyting itself.
        return [];
    }
    // Otherwise just force the correct indentation
    // This works in all cases. The cases above are just to improve user experience a bit
    const newIdent = startInfo.indentation + makeTab(options);
    const lineStart = new vscode.Position(position.line, 0);
    return [ vscode.TextEdit.replace(new vscode.Range(lineStart, position), newIdent) ];
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

function findOuterBlockStart(document: vscode.TextDocument, start: number): LineInfo | undefined {
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
        n -= 1;
    }
    return undefined;
}

function testBlockStart(line: vscode.TextLine): LineInfo | undefined {
    const matches = /^(\s*)(?:begin|if|else|elsif|while|either|or|with|define|macro|procedure)\b.*/g.exec(line.text);
    return matches ? new LineInfo(line, matches[1]) : undefined;
}

function testBlockEnd(line: vscode.TextLine): LineInfo | undefined {
    const matches = /^(\s*)(?:end|else|elsif|or)\b.*/g.exec(line.text);
    return matches ? new LineInfo(line, matches[1]) : undefined;
}

function makeTab(options: vscode.FormattingOptions): string {
    if (!options.insertSpaces) {
        return '\t';
    }
    if (options.tabSize < SPACES.length) {
        return SPACES[options.tabSize];
    }
    let len = SPACES.length - 1;
    const spaces = SPACES.slice(SPACES.length - 1);
    while (len < options.tabSize) {
        len += 1;
        spaces.push(' ');
    }
    return spaces.join('');
}

function indentationLen(str: string, options: vscode.FormattingOptions): number {
    let len = 0;
    for (const ch of str) {
        if (ch === ' ') {
            len += 1;
        } else if (ch === '\t') {
            len += options.tabSize;
        } else {
            break;
        }
    }
    return len;
}
