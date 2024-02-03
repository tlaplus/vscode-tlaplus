import * as vscode from 'vscode';
import { moduleSearchPaths, ModuleSearchPathSource } from '../paths';

const sourceIcon = new vscode.ThemeIcon('folder-library');
const zipDirIcon = new vscode.ThemeIcon('file-zip');
const folderIcon = new vscode.ThemeIcon('folder');

class mspSource extends vscode.TreeItem {
    level = 'source';
    constructor(
        public source: ModuleSearchPathSource
    ) {
        super(source.description, vscode.TreeItemCollapsibleState.Expanded);
    }
    iconPath = sourceIcon;
}

class mspPath extends vscode.TreeItem {
    level = 'path';
    constructor(
        path: string
    ) {
        super(path, vscode.TreeItemCollapsibleState.None);
        this.iconPath = path.startsWith('jar://') ? zipDirIcon : folderIcon;
    }
}

type msp = mspSource | mspPath

export class ModuleSearchPathsTreeDataProvider implements vscode.TreeDataProvider<msp> {
    static readonly viewType = 'tlaplus.module-search-paths';
    private _onDidChangeTreeData = new vscode.EventEmitter<msp | msp[] | undefined | null | void>();
    readonly onDidChangeTreeData = this._onDidChangeTreeData.event;

    constructor(
        private context: vscode.ExtensionContext
    ) {
        context.subscriptions.push(moduleSearchPaths.updates(_ => {
            this._onDidChangeTreeData.fire();
        }));
    }

    getChildren(element?: msp): Thenable<msp[]> {
        if (!element) {
            return Promise.resolve(
                moduleSearchPaths.getSources().map(s => new mspSource(s))
            );
        }
        if (element.level === 'source') {
            return Promise.resolve(
                moduleSearchPaths.getSourcePaths((element as mspSource).source.name).map(p => new mspPath(p))
            );
        }
        return Promise.resolve([]);
    }

    getTreeItem(element: msp): vscode.TreeItem {
        return element;
    }
}
