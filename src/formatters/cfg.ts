import * as vscode from 'vscode';
import { IndentationType, LineInfo, indentRight } from './formatting';

export class CfgOnTypeFormattingEditProvider implements vscode.OnTypeFormattingEditProvider {
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
        const prevLine = document.lineAt(position.line - 1);
        const startInfo = testBlockStart(prevLine);
        if (!startInfo) {
            return [];
        }
        const lineText = document.lineAt(position.line).text;
        return indentRight(lineText, position, startInfo.indentation, options);
    }
}

function testBlockStart(line: vscode.TextLine): LineInfo | undefined {
    // eslint-disable-next-line max-len
    const regex = /^(\s*)(?:SPECIFICATION|INVARIANT(S)?|PROPERT(Y|IES)|CONSTANT(S)?|INIT|NEXT|SYMMETRY|CONSTRAINT(S)?|ACTION_CONSTRAINT(S)?|VIEW|CHECK_DEADLOCK|POSTCONDITION)\s*$/g;
    const gMatches = regex.exec(line.text);
    return gMatches ? new LineInfo(line, gMatches[1], IndentationType.Right) : undefined;
}
