import * as vscode from 'vscode';
import { TlaDocumentInfos, TlaDocumentInfo } from '../model/documentInfo';

function symbolLocations(document: vscode.TextDocument, docInfo: TlaDocumentInfo, position: vscode.Position) {
    const range = document.getWordRangeAtPosition(position);
    if (!range) {
        return undefined;
    }
    const word = document.lineAt(position.line).text.substring(range.start.character, range.end.character);
    const symbols = docInfo.isPlusCalAt(position)
        ? docInfo.symbols.concat(docInfo.plusCalSymbols)
        : docInfo.symbols;
    const locations = [];
    for (const symbol of symbols) {
        if (symbol.name === word && symbol.location.range.start.isBeforeOrEqual(range.start)) {
            locations.push(symbol.location);
        }
    }
    return locations;
}

export class TlaDeclarationsProvider implements vscode.DeclarationProvider {
    constructor(
        private readonly docInfos: TlaDocumentInfos
    ) { }

    provideDeclaration(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.Declaration> {
        const docInfo = this.docInfos.get(document.uri);
        return docInfo ? symbolLocations(document, docInfo, position) : undefined;
    }
}

export class TlaDefinitionsProvider implements vscode.DefinitionProvider {
    constructor(
        private readonly docInfos: TlaDocumentInfos
    ) { }

    provideDefinition(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.Declaration> {
        const docInfo = this.docInfos.get(document.uri);
        return docInfo ? symbolLocations(document, docInfo, position) : undefined;
    }
}
