import * as vscode from 'vscode';

/**
 * Various information about a TLA module.
 */
export class TlaDocumentInfo {
    private symbols: vscode.SymbolInformation[] = [];
    private plusCalRange: vscode.Range | undefined;

    setSymbols(symbols: vscode.SymbolInformation[]) {
        this.symbols = symbols;
    }

    getSymbols(): ReadonlyArray<vscode.SymbolInformation> {
        return this.symbols;
    }

    setPlusCalRange(range: vscode.Range) {
        this.plusCalRange = range;
    }

    getPlusCalRange(): vscode.Range | undefined {
        return this.plusCalRange;
    }
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
