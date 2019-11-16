import * as vscode from 'vscode';

const ZERO_POSITION = new vscode.Position(0, 0);

class DocInfo {
    constructor(
        readonly lines: string[],
        readonly position: vscode.Position,
        readonly char: string
    ) {}
}

export async function replaceDocContents(doc: vscode.TextDocument, content: string): Promise<boolean> {
    const edits = [];
    if (doc.lineCount > 0) {
        const lastLine = doc.lineAt(doc.lineCount - 1);
        const delEdit = vscode.TextEdit.delete(new vscode.Range(ZERO_POSITION, lastLine.range.end));
        edits.push(delEdit);
    }
    edits.push(vscode.TextEdit.insert(ZERO_POSITION, content));
    return applyDocEdits(doc.uri, edits);
}

export async function applyDocEdits(docUri: vscode.Uri, edits: vscode.TextEdit[] | null | undefined): Promise<boolean> {
    if (!edits) {
        return false;
    }
    const wsEdit = new vscode.WorkspaceEdit();
    for (const edit of edits) {
        wsEdit.replace(docUri, edit.range, edit.newText);
    }
    return vscode.workspace.applyEdit(wsEdit);
}

export function parseDocInfo(lines: string[]): DocInfo {
    let position;
    let char;
    let n = 0;
    const clearLines = lines.map(line => {
        let eLine = line;
        const matches = /^(.*)\${(\w+)}(.*)$/g.exec(line);
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
