import * as vscode from 'vscode';
import { TlaDocumentInfos } from '../model/documentInfo';

export class TlaDeclarationsProvider implements vscode.DeclarationProvider {
    constructor(
        private docInfos: TlaDocumentInfos
    ) {}

    provideDeclaration(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.Declaration> {
        const docInfo = this.docInfos.get(document.uri);
        if (!docInfo) {
            return undefined;
        }
        const range = document.getWordRangeAtPosition(position);
        if (!range) {
            return undefined;
        }
        const word = document.lineAt(position.line).text.substring(range.start.character, range.end.character);
        const symbols = docInfo.plusCalRange && docInfo.plusCalRange.contains(position)
            ? docInfo.plusCalSymbols
            : docInfo.symbols;
        const locations = [];
        for (const symbol of symbols) {
            if (symbol.name === word) {
                locations.push(symbol.location);
            }
        }
        return locations;
    }
}
