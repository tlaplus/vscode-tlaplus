import { TextDocument, Position } from 'vscode';

export function getPrevText(document: TextDocument, position: Position): string {
    if (position.character === 0) {
        return '';
    }
    const prevText = document.lineAt(position.line).text.substring(0, position.character);
    return prevText;
}
