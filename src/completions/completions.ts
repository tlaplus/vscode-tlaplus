import { TextDocument, Position } from 'vscode';

export function getPrevText(document: TextDocument, position: Position): string {
    return position.character === 0
        ? ''
        : document.lineAt(position.line).text.substring(0, position.character);
}
