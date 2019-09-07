import * as vscode from 'vscode';
import * as assert from 'assert';

const ZERO_POSITION = new vscode.Position(0, 0);

export const OPT_4_SPACES: vscode.FormattingOptions = { insertSpaces: true, tabSize: 4 };
export const OPT_2_SPACES: vscode.FormattingOptions = { insertSpaces: true, tabSize: 2 };
export const OPT_7_SPACES: vscode.FormattingOptions = { insertSpaces: true, tabSize: 7 };
export const OPT_TABS: vscode.FormattingOptions = { insertSpaces: false, tabSize: 4 };

class DocInfo {
    constructor(
        readonly lines: string[],
        readonly position: vscode.Position,
        readonly char: string
    ) {}
}

export async function assertOnTypeFormatting(
    formatter: vscode.OnTypeFormattingEditProvider,
    doc: vscode.TextDocument,
    docLines: string[],
    expectLines: string[],
    options: vscode.FormattingOptions
): Promise<void> {
    const docInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, docInfo.lines.join('\n'));
    const tokenSrc = new vscode.CancellationTokenSource();
    const edits = await formatter.provideOnTypeFormattingEdits(
        doc,
        docInfo.position,
        docInfo.char,
        options,
        tokenSrc.token
    );
    await applyDocEdits(doc.uri, edits);
    assert.deepEqual(doc.getText().split('\n'), expectLines);
    return undefined;
}

async function replaceDocContents(doc: vscode.TextDocument, content: string): Promise<boolean> {
    const edits = [];
    if (doc.lineCount > 0) {
        const lastLine = doc.lineAt(doc.lineCount - 1);
        const delEdit = vscode.TextEdit.delete(new vscode.Range(ZERO_POSITION, lastLine.range.end));
        edits.push(delEdit);
    }
    edits.push(vscode.TextEdit.insert(ZERO_POSITION, content));
    return applyDocEdits(doc.uri, edits);
}

async function applyDocEdits(docUri: vscode.Uri, edits: vscode.TextEdit[] | null | undefined): Promise<boolean> {
    if (!edits) {
        return false;
    }
    const wsEdit = new vscode.WorkspaceEdit();
    for (const edit of edits) {
        wsEdit.replace(docUri, edit.range, edit.newText);
    }
    return vscode.workspace.applyEdit(wsEdit);
}

function parseDocInfo(lines: string[]): DocInfo {
    let position;
    let char;
    let n = 0;
    const clearLines = lines.map(line => {
        let eLine = line;
        const matches = /^(.*){(\w+)}(.*)$/g.exec(line);
        if (matches) {
            char = matches[2] === 'enter' ? '\n' : matches[2];
            position = new vscode.Position(n, matches[1].length);
            eLine = matches[1] + (char === '\n' ? '' : char) + matches[3];
        }
        n += 1;
        return eLine;
    });
    if (!position || !char) {
        throw new Error('Caret position not found.');
    }
    return new DocInfo(clearLines, position, char);
}
