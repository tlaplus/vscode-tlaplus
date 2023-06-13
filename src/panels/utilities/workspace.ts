import * as vscode from 'vscode';

export function revealFile(filePath: string, viewColumn: vscode.ViewColumn, line: number, character: number) {
    const location = new vscode.Position(line, character);
    const showOpts: vscode.TextDocumentShowOptions = {
        selection: new vscode.Range(location, location),
        viewColumn: viewColumn
    };
    vscode.workspace.openTextDocument(filePath)
        .then(doc => vscode.window.showTextDocument(doc, showOpts));
}

export async function createDocument(text: string) {
    const doc = await vscode.workspace.openTextDocument();
    const editor = await vscode.window.showTextDocument(doc, vscode.ViewColumn.One);
    const zero = new vscode.Position(0, 0);
    await editor.edit((edit) => edit.insert(zero, text));
    editor.selection = new vscode.Selection(zero, zero);
    editor.revealRange(new vscode.Range(zero, zero), vscode.TextEditorRevealType.AtTop);
}
