import * as vscode from 'vscode';
import { JarModuleReader, ModuleInfo } from '../utils/jarReader';
import { ModuleSymbolProvider, ModuleSymbol } from '../symbols/moduleSymbolProvider';

/**
 * Tree item representing a module, category, or symbol in the module explorer.
 */
export class ModuleTreeItem extends vscode.TreeItem {
    constructor(
        public readonly label: string,
        public readonly itemType: 'category' | 'module' | 'symbol',
        public readonly collapsibleState: vscode.TreeItemCollapsibleState,
        public readonly moduleInfo?: ModuleInfo,
        public readonly symbol?: ModuleSymbol,
        public readonly category?: 'standard' | 'community'
    ) {
        super(label, collapsibleState);

        // Set context value for commands
        this.contextValue = itemType;

        // Set icons
        switch (itemType) {
            case 'category':
                this.iconPath = new vscode.ThemeIcon(
                    category === 'standard' ? 'library' : 'package'
                );
                break;
            case 'module':
                this.iconPath = new vscode.ThemeIcon('file-code');
                break;
            case 'symbol':
                if (symbol) {
                    this.iconPath = new vscode.ThemeIcon(
                        symbol.kind === vscode.SymbolKind.Function ? 'symbol-method' :
                            symbol.kind === vscode.SymbolKind.Constant ? 'symbol-constant' :
                                'symbol-variable'
                    );
                }
                break;
        }

        // Set tooltip
        if (moduleInfo) {
            this.tooltip = `${moduleInfo.name} - ${moduleInfo.category} module`;
        } else if (symbol) {
            this.tooltip = symbol.documentation || `${symbol.name} from ${symbol.module}`;
        }

        // Set description
        if (itemType === 'module' && moduleInfo) {
            this.description = `${moduleInfo.category}`;
        } else if (itemType === 'symbol' && symbol) {
            if (symbol.arity && symbol.arity > 0) {
                this.description = `(${Array(symbol.arity).fill('_').join(', ')})`;
            }
        }

        // Set command for modules
        if (itemType === 'module' && moduleInfo) {
            this.command = {
                command: 'tlaplus.viewModuleSource',
                title: 'View Module Source',
                arguments: [this]
            };
        }
    }
}

/**
 * Tree data provider for the TLA+ Module Explorer.
 */
export class ModuleExplorerTreeProvider implements vscode.TreeDataProvider<ModuleTreeItem> {
    private _onDidChangeTreeData: vscode.EventEmitter<ModuleTreeItem | undefined | null | void> =
        new vscode.EventEmitter<ModuleTreeItem | undefined | null | void>();
    readonly onDidChangeTreeData: vscode.Event<ModuleTreeItem | undefined | null | void> =
        this._onDidChangeTreeData.event;

    private standardModules: ModuleInfo[] = [];
    private communityModules: ModuleInfo[] = [];
    private moduleSymbols = new Map<string, ModuleSymbol[]>();
    private isLoading = false;
    private searchPattern = '';

    constructor(
        private readonly jarReader: JarModuleReader,
        private readonly symbolProvider: ModuleSymbolProvider,
        private readonly toolsJarPath: string,
        private readonly communityJarPath: string
    ) {}

    /**
     * Refreshes the tree view data.
     */
    async refresh(): Promise<void> {
        this.isLoading = true;
        this._onDidChangeTreeData.fire();

        try {
            // Load modules
            const allStandardModules = await this.jarReader.listModules(this.toolsJarPath);
            const allCommunityModules = await this.jarReader.listModules(this.communityJarPath);

            this.standardModules = allStandardModules.filter(m => m.category === 'standard');
            this.communityModules = allCommunityModules.filter(m => m.category === 'community');

            // Clear symbol cache
            this.moduleSymbols.clear();
        } finally {
            this.isLoading = false;
            this._onDidChangeTreeData.fire();
        }
    }

    /**
     * Sets a search pattern to filter modules and symbols.
     */
    setSearchPattern(pattern: string): void {
        this.searchPattern = pattern.toLowerCase();
        this._onDidChangeTreeData.fire();
    }

    /**
     * Gets tree item for display.
     */
    getTreeItem(element: ModuleTreeItem): vscode.TreeItem {
        return element;
    }

    /**
     * Gets children for a tree item.
     */
    async getChildren(element?: ModuleTreeItem): Promise<ModuleTreeItem[]> {
        if (this.isLoading) {
            return [];
        }

        if (!element) {
            // Root level - show categories
            const items: ModuleTreeItem[] = [];

            if (this.standardModules.length > 0) {
                const standardItem = new ModuleTreeItem(
                    `Standard Modules (${this.standardModules.length})`,
                    'category',
                    vscode.TreeItemCollapsibleState.Expanded,
                    undefined,
                    undefined,
                    'standard'
                );
                items.push(standardItem);
            }

            if (this.communityModules.length > 0) {
                const communityItem = new ModuleTreeItem(
                    `Community Modules (${this.communityModules.length})`,
                    'category',
                    vscode.TreeItemCollapsibleState.Collapsed,
                    undefined,
                    undefined,
                    'community'
                );
                items.push(communityItem);
            }

            return items;
        }

        if (element.itemType === 'category') {
            // Show modules in category
            const modules = element.category === 'standard'
                ? this.standardModules
                : this.communityModules;

            return modules
                .filter(m => this.matchesSearch(m.name))
                .sort((a, b) => a.name.localeCompare(b.name))
                .map(module => new ModuleTreeItem(
                    module.name,
                    'module',
                    vscode.TreeItemCollapsibleState.Collapsed,
                    module
                ));
        }

        if (element.itemType === 'module' && element.moduleInfo) {
            // Show symbols in module
            const symbols = await this.getModuleSymbols(element.moduleInfo.name);

            // Group symbols by kind
            const operators = symbols.filter(s => s.kind === vscode.SymbolKind.Function);
            const constants = symbols.filter(s => s.kind === vscode.SymbolKind.Constant);
            const variables = symbols.filter(s => s.kind === vscode.SymbolKind.Variable);

            const items: ModuleTreeItem[] = [];

            // Add operators
            for (const op of operators.filter(s => this.matchesSearch(s.name))) {
                items.push(new ModuleTreeItem(
                    op.name,
                    'symbol',
                    vscode.TreeItemCollapsibleState.None,
                    undefined,
                    op
                ));
            }

            // Add constants
            for (const constant of constants.filter(s => this.matchesSearch(s.name))) {
                items.push(new ModuleTreeItem(
                    constant.name,
                    'symbol',
                    vscode.TreeItemCollapsibleState.None,
                    undefined,
                    constant
                ));
            }

            // Add variables
            for (const variable of variables.filter(s => this.matchesSearch(s.name))) {
                items.push(new ModuleTreeItem(
                    variable.name,
                    'symbol',
                    vscode.TreeItemCollapsibleState.None,
                    undefined,
                    variable
                ));
            }

            return items;
        }

        return [];
    }

    /**
     * Gets or loads symbols for a module.
     */
    private async getModuleSymbols(moduleName: string): Promise<ModuleSymbol[]> {
        const cached = this.moduleSymbols.get(moduleName);
        if (cached) {
            return cached;
        }

        const symbols = await this.symbolProvider.getSymbolsForModule(moduleName);
        this.moduleSymbols.set(moduleName, symbols);
        return symbols;
    }

    /**
     * Checks if a name matches the current search pattern.
     */
    private matchesSearch(name: string): boolean {
        if (!this.searchPattern) {
            return true;
        }
        return name.toLowerCase().includes(this.searchPattern);
    }

    /**
     * Gets parent of a tree item (for reveal functionality).
     */
    getParent(element: ModuleTreeItem): vscode.ProviderResult<ModuleTreeItem> {
        // Not implemented as we don't need reveal functionality
        return undefined;
    }
}

/**
 * Manages the Module Explorer panel.
 */
export class ModuleExplorerPanel {
    private treeView: vscode.TreeView<ModuleTreeItem>;
    private searchBox: vscode.QuickPick<vscode.QuickPickItem> | undefined;

    constructor(
        private readonly context: vscode.ExtensionContext,
        private readonly treeDataProvider: ModuleExplorerTreeProvider
    ) {
        // Create tree view
        this.treeView = vscode.window.createTreeView('tlaModuleExplorer', {
            treeDataProvider: this.treeDataProvider,
            showCollapseAll: true
        });

        // Register tree view
        context.subscriptions.push(this.treeView);

        // Register commands
        this.registerCommands();

        // Initial refresh
        this.treeDataProvider.refresh();
    }

    /**
     * Registers commands for the module explorer.
     */
    private registerCommands(): void {
        // Refresh command
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.moduleExplorer.refresh', () => {
                this.treeDataProvider.refresh();
            })
        );

        // Search command
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.moduleExplorer.search', () => {
                this.showSearchBox();
            })
        );

        // Clear search command
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.moduleExplorer.clearSearch', () => {
                this.treeDataProvider.setSearchPattern('');
            })
        );

        // View module source command
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.viewModuleSource', async (item?: ModuleTreeItem | ModuleInfo) => {
                let moduleInfo: ModuleInfo | undefined;

                // Handle both TreeItem and direct ModuleInfo
                if (item instanceof ModuleTreeItem) {
                    moduleInfo = item.moduleInfo;
                } else if (item && 'name' in item && 'category' in item) {
                    moduleInfo = item as ModuleInfo;
                }

                if (!moduleInfo) {
                    vscode.window.showErrorMessage('Module information not provided');
                    return;
                }

                try {
                    const uri = vscode.Uri.parse(`tla-module://${moduleInfo.category}/${moduleInfo.name}.tla`);
                    const doc = await vscode.workspace.openTextDocument(uri);
                    await vscode.window.showTextDocument(doc, { preview: false });
                } catch (error) {
                    vscode.window.showErrorMessage(`Failed to open module source: ${error}`);
                }
            })
        );

        // Insert extends command
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.moduleExplorer.insertExtends', async (item: ModuleTreeItem) => {
                if (item && item.moduleInfo) {
                    await this.insertExtendsStatement(item.moduleInfo.name);
                } else {
                    vscode.window.showErrorMessage('No module selected');
                }
            })
        );

        // Insert symbol command
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.moduleExplorer.insertSymbol', async (item: ModuleTreeItem) => {
                if (item.symbol) {
                    await this.insertSymbol(item.symbol);
                }
            })
        );

        // Copy symbol name command
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.moduleExplorer.copySymbolName', async (item: ModuleTreeItem) => {
                if (item.symbol) {
                    await vscode.env.clipboard.writeText(item.symbol.name);
                    vscode.window.showInformationMessage(`Copied "${item.symbol.name}" to clipboard`);
                }
            })
        );
    }

    /**
     * Shows the search box for filtering modules and symbols.
     */
    private showSearchBox(): void {
        const input = vscode.window.createQuickPick();
        input.placeholder = 'Search modules and symbols...';
        input.value = this.treeDataProvider['searchPattern'];

        input.onDidChangeValue(value => {
            this.treeDataProvider.setSearchPattern(value);
        });

        input.onDidAccept(() => {
            input.hide();
        });

        input.onDidHide(() => {
            input.dispose();
        });

        input.show();
    }

    /**
     * Inserts an EXTENDS statement for the given module.
     */
    private async insertExtendsStatement(moduleName: string): Promise<void> {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showWarningMessage('No active editor');
            return;
        }

        const document = editor.document;
        const text = document.getText();

        // Check if module is already extended
        const extendsRegex = /EXTENDS\s+([^-\n]+)/g;
        let match;
        while ((match = extendsRegex.exec(text)) !== null) {
            const modules = match[1].split(',').map(m => m.trim());
            if (modules.includes(moduleName)) {
                vscode.window.showInformationMessage(`Module ${moduleName} is already extended`);
                return;
            }
        }

        // Find or create EXTENDS line
        const extendsMatch = text.match(/EXTENDS\s+([^-\n]+)/);
        if (extendsMatch) {
            // Add to existing EXTENDS
            const matchIndex = extendsMatch.index || 0;
            const start = document.positionAt(matchIndex + extendsMatch[0].length);
            await editor.edit(editBuilder => {
                editBuilder.insert(start, `, ${moduleName}`);
            });
        } else {
            // Find module header
            const moduleMatch = text.match(/----\s*MODULE\s+\w+\s*----/);
            if (moduleMatch) {
                const moduleMatchIndex = moduleMatch.index || 0;
                const moduleEnd = document.positionAt(moduleMatchIndex + moduleMatch[0].length);
                const nextLine = new vscode.Position(moduleEnd.line + 1, 0);
                await editor.edit(editBuilder => {
                    editBuilder.insert(nextLine, `EXTENDS ${moduleName}\n\n`);
                });
            }
        }

        vscode.window.showInformationMessage(`Added ${moduleName} to EXTENDS`);
    }

    /**
     * Inserts a symbol at the current cursor position.
     */
    private async insertSymbol(symbol: ModuleSymbol): Promise<void> {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showWarningMessage('No active editor');
            return;
        }

        let insertText = symbol.name;
        if (symbol.arity && symbol.arity > 0) {
            const params = Array(symbol.arity).fill('').map((_, i) => `\${${i + 1}:arg${i + 1}}`).join(', ');
            insertText = `${symbol.name}(${params})`;
        }

        await editor.insertSnippet(new vscode.SnippetString(insertText));
    }
}