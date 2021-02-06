import * as vscode from 'vscode';

/**
 * Describes a module, which can be:
 * - real TLA+ module
 * - PlusCal algorithm
 * - .tla file contents that is outside of modules and pluscal algorithms
 */
export class Module {
    constructor(
        readonly name: string,
        readonly symbols: vscode.SymbolInformation[] = [],
        readonly range: vscode.Range
    ) {}
}

/**
 * Various information about a TLA document.
 */
export class TlaDocumentInfo {
    readonly plusCalSymbols: vscode.SymbolInformation[];

    constructor(
        private rootModule: Module | undefined = undefined,
        private plusCal: Module | undefined = undefined,
        private modules: Module[] = [],
        public symbols: vscode.SymbolInformation[] = []
    ) {
        this.plusCalSymbols = plusCal?.symbols || [];
    }

    isPlusCalAt(pos: vscode.Position): boolean {
        return this.plusCal && this.plusCal.range.contains(pos) ? true : false;
    }
}

export class TlaDocumentInfos {
    private readonly map = new Map<vscode.Uri, TlaDocumentInfo>();

    get(uri: vscode.Uri): TlaDocumentInfo {
        let docInfo = this.map.get(uri);
        if (!docInfo) {
            docInfo = new TlaDocumentInfo();
            this.map.set(uri, docInfo);
        }
        return docInfo;
    }

    set(uri: vscode.Uri, docInfo: TlaDocumentInfo): void {
        this.map.set(uri, docInfo);
    }
}
