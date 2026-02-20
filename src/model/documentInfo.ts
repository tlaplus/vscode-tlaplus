import * as vscode from 'vscode';

export type ModuleExtendsGraph = Map<string, string[]>;

export interface XmlModuleDependencies {
    rootModuleName?: string;
    extendsGraph: ModuleExtendsGraph;
}

function cloneExtendsGraph(graph: ModuleExtendsGraph): ModuleExtendsGraph {
    const cloned: ModuleExtendsGraph = new Map();
    for (const [moduleName, extendsList] of graph.entries()) {
        cloned.set(moduleName, extendsList.slice());
    }
    return cloned;
}

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
    private readonly xmlDependencies: XmlModuleDependencies;

    constructor(
        private readonly rootModule: Module | undefined = undefined,
        private readonly plusCal: Module | undefined = undefined,
        private readonly modules: Module[] = [],
        public symbols: vscode.SymbolInformation[] = [],
        xmlDependencies: XmlModuleDependencies = { extendsGraph: new Map<string, string[]>() }
    ) {
        this.plusCalSymbols = plusCal?.symbols || [];
        this.xmlDependencies = {
            rootModuleName: xmlDependencies.rootModuleName,
            extendsGraph: cloneExtendsGraph(xmlDependencies.extendsGraph)
        };
    }

    isPlusCalAt(pos: vscode.Position): boolean {
        return this.plusCal && this.plusCal.range.contains(pos) ? true : false;
    }

    getRootModuleName(): string | undefined {
        return this.xmlDependencies.rootModuleName;
    }

    getExtendedModules(moduleName: string): string[] {
        return this.xmlDependencies.extendsGraph.get(moduleName)?.slice() ?? [];
    }

    getExtendsGraph(): ModuleExtendsGraph {
        return cloneExtendsGraph(this.xmlDependencies.extendsGraph);
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
