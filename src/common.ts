import * as vscode from 'vscode';

export function pathToUri(path: string): vscode.Uri {
    return vscode.Uri.parse('file://' + path);
}
