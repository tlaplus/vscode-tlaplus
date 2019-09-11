import * as vscode from 'vscode';

const SPACES = ['', ' ', '  ', '   ', '    ', '     ', '      ', '       ', '        '];

export enum IndentationType {
    Exact,      // Indent exactly to the given length
    Right,      // Increase indentation
    Left        // Decrease indentation
}

export class LineInfo {
    constructor(
        readonly line: vscode.TextLine,
        readonly indentation: string,
        readonly indentationType: IndentationType
    ) {}
}

/**
 * Adds tab to the given line.
 */
export function indentRight(
    lineText: string,
    position: vscode.Position,
    baseIndentation: string,
    options: vscode.FormattingOptions
): vscode.TextEdit[] {
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

/**
 * Indents the block with the given indentation string.
 */
export function indentExact(
    lineText: string,
    position: vscode.Position,
    indentation: string
): vscode.TextEdit[] {
    if (lineText === indentation) {
        return [];
    }
    const lineStart = new vscode.Position(position.line, 0);
    return [ vscode.TextEdit.replace(new vscode.Range(lineStart, position), indentation) ];
}

export function makeSpaces(num: number) {
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

export function indentationLen(str: string, options: vscode.FormattingOptions): number {
    let len = 0;
    for (const ch of str) {
        len += ch === '\t' ? options.tabSize : 1;
    }
    return len;
}

function makeTab(options: vscode.FormattingOptions): string {
    return options.insertSpaces ? makeSpaces(options.tabSize) : '\t';
}
