import * as vscode from 'vscode';

/**
 * Various information about a TLA module.
 */
export class TlaDocumentInfo {
    symbols: vscode.SymbolInformation[] = [];
    plusCalSymbols: vscode.SymbolInformation[] = [];
    plusCalRange: vscode.Range | undefined;
}

export class TlaDocumentInfos {
    private map = new Map<vscode.Uri, TlaDocumentInfo>();

    get(uri: vscode.Uri): TlaDocumentInfo {
        let docInfo = this.map.get(uri);
        if (!docInfo) {
            docInfo = new TlaDocumentInfo();
            this.map.set(uri, docInfo);
        }
        return docInfo;
    }
}
