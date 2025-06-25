import * as vscode from 'vscode';
import { JarModuleReader, ModuleInfo } from '../utils/jarReader';
import { ModuleSymbolProvider, ModuleSymbol } from '../symbols/moduleSymbolProvider';

interface ModuleQuickPickItem extends vscode.QuickPickItem {
    module?: ModuleInfo;
    symbol?: ModuleSymbol;
    action?: 'back' | 'insert' | 'view' | 'standard' | 'community' | 'search' | 'operators';
}

/**
 * Provides UI for browsing and discovering TLA+ modules.
 */
export class ModuleExplorer {
    constructor(
        private readonly jarReader: JarModuleReader,
        private readonly symbolProvider: ModuleSymbolProvider,
        private readonly toolsJarPath: string,
        private readonly communityJarPath: string
    ) {}

    /**
     * Shows the module explorer quick pick interface.
     */
    async showModuleExplorer(): Promise<void> {
        await this.showMainMenu();
    }

    /**
     * Shows the main menu with module categories.
     */
    private async showMainMenu(): Promise<void> {
        const items: ModuleQuickPickItem[] = [
            {
                label: '$(library) Standard Modules',
                description: 'Built-in TLA+ modules',
                detail: 'Integers, Sequences, FiniteSets, TLC, and more',
                action: 'standard'
            },
            {
                label: '$(package) Community Modules',
                description: 'Community-contributed modules',
                detail: 'Extended functionality from the TLA+ community',
                action: 'community'
            },
            {
                label: '$(search) Search All Modules',
                description: 'Search for modules and operators',
                detail: 'Find modules by name or operator',
                action: 'search'
            },
            {
                label: '$(symbol-namespace) Browse All Operators',
                description: 'View all available operators',
                detail: 'Alphabetical list of all operators with their source modules',
                action: 'operators'
            }
        ];

        const selected = await vscode.window.showQuickPick(items, {
            placeHolder: 'TLA+ Module Explorer',
            matchOnDescription: true,
            matchOnDetail: true
        });

        if (!selected) {
            return;
        }

        switch (selected.action) {
            case 'standard':
                await this.showModuleList('standard');
                break;
            case 'community':
                await this.showModuleList('community');
                break;
            case 'search':
                await this.showSearchInterface();
                break;
            case 'operators':
                await this.showAllOperators();
                break;
        }
    }

    /**
     * Shows a list of modules for a specific category.
     */
    private async showModuleList(category: 'standard' | 'community' | 'tlaps'): Promise<void> {
        const jarPath = category === 'standard' ? this.toolsJarPath : this.communityJarPath;
        const modules = await this.jarReader.listModules(jarPath);
        const categoryModules = modules.filter(m => m.category === category);

        const items: ModuleQuickPickItem[] = [
            {
                label: '$(arrow-left) Back',
                description: 'Return to main menu',
                action: 'back'
            }
        ];

        // Add module items
        for (const module of categoryModules.sort((a, b) => a.name.localeCompare(b.name))) {
            const symbols = await this.symbolProvider.getSymbolsForModule(module.name);
            const operatorCount = symbols.filter(s => s.kind === vscode.SymbolKind.Function).length;
            const constantCount = symbols.filter(s => s.kind === vscode.SymbolKind.Constant).length;

            items.push({
                label: `$(file-code) ${module.name}`,
                description: `${operatorCount} operators, ${constantCount} constants`,
                detail: this.getModuleDescription(module.name),
                module: module
            });
        }

        const quickPick = vscode.window.createQuickPick<ModuleQuickPickItem>();
        const categoryName = category === 'standard' ? 'Standard' : 'Community';
        quickPick.placeholder = `${categoryName} Modules (${categoryModules.length} modules)`;
        quickPick.items = items;
        quickPick.matchOnDescription = true;
        quickPick.matchOnDetail = true;

        quickPick.onDidAccept(async () => {
            const selected = quickPick.activeItems[0];
            if (!selected) {
                return;
            }

            quickPick.hide();

            if (selected.action === 'back') {
                await this.showMainMenu();
            } else if (selected.module) {
                await this.showModuleDetails(selected.module);
            }
        });

        quickPick.show();
    }

    /**
     * Shows detailed information about a specific module.
     */
    private async showModuleDetails(module: ModuleInfo): Promise<void> {
        const symbols = await this.symbolProvider.getSymbolsForModule(module.name);

        const items: ModuleQuickPickItem[] = [
            {
                label: '$(arrow-left) Back',
                description: 'Return to module list',
                action: 'back'
            },
            {
                label: '$(add) Insert EXTENDS Statement',
                description: `Add "EXTENDS ${module.name}" to current file`,
                action: 'insert',
                module: module
            },
            {
                label: '$(eye) View Module Source',
                description: 'Open the module source code',
                action: 'view',
                module: module
            },
            {
                label: '',
                kind: vscode.QuickPickItemKind.Separator
            }
        ];

        // Group symbols by kind
        const operators = symbols.filter(s => s.kind === vscode.SymbolKind.Function);
        const constants = symbols.filter(s => s.kind === vscode.SymbolKind.Constant);
        const variables = symbols.filter(s => s.kind === vscode.SymbolKind.Variable);

        // Add operators
        if (operators.length > 0) {
            items.push({
                label: 'Operators',
                kind: vscode.QuickPickItemKind.Separator
            });
            for (const op of operators.sort((a, b) => a.name.localeCompare(b.name))) {
                const signature = op.arity ? `(${Array(op.arity).fill('_').join(', ')})` : '';
                items.push({
                    label: `$(symbol-method) ${op.name}${signature}`,
                    description: op.documentation?.split('\n')[0],
                    symbol: op
                });
            }
        }

        // Add constants
        if (constants.length > 0) {
            items.push({
                label: 'Constants',
                kind: vscode.QuickPickItemKind.Separator
            });
            for (const constant of constants.sort((a, b) => a.name.localeCompare(b.name))) {
                items.push({
                    label: `$(symbol-constant) ${constant.name}`,
                    description: constant.documentation?.split('\n')[0],
                    symbol: constant
                });
            }
        }

        // Add variables
        if (variables.length > 0) {
            items.push({
                label: 'Variables',
                kind: vscode.QuickPickItemKind.Separator
            });
            for (const variable of variables.sort((a, b) => a.name.localeCompare(b.name))) {
                items.push({
                    label: `$(symbol-variable) ${variable.name}`,
                    description: variable.documentation?.split('\n')[0],
                    symbol: variable
                });
            }
        }

        const quickPick = vscode.window.createQuickPick<ModuleQuickPickItem>();
        quickPick.placeholder = `Module: ${module.name}`;
        quickPick.items = items;
        quickPick.matchOnDescription = true;

        quickPick.onDidAccept(async () => {
            const selected = quickPick.activeItems[0];
            if (!selected) {
                return;
            }

            quickPick.hide();

            if (selected.action === 'back') {
                await this.showModuleList(module.category);
            } else if (selected.action === 'insert') {
                await this.insertExtendsStatement(module.name);
            } else if (selected.action === 'view') {
                await this.viewModuleSource(module);
            } else if (selected.symbol) {
                await this.showSymbolDetails(selected.symbol);
            }
        });

        quickPick.show();
    }

    /**
     * Shows the search interface for finding modules and operators.
     */
    private async showSearchInterface(): Promise<void> {
        const input = await vscode.window.showInputBox({
            prompt: 'Search for modules or operators',
            placeHolder: 'e.g., "Seq" or "Append"',
            validateInput: (value) => {
                return value.length < 2 ? 'Enter at least 2 characters' : undefined;
            }
        });

        if (!input) {
            await this.showMainMenu();
            return;
        }

        // Search for modules and symbols
        const allModules: ModuleInfo[] = [];
        allModules.push(...await this.jarReader.listModules(this.toolsJarPath));
        allModules.push(...await this.jarReader.listModules(this.communityJarPath));

        const matchingModules = allModules.filter(m =>
            m.name.toLowerCase().includes(input.toLowerCase())
        );

        const matchingSymbols = await this.symbolProvider.searchSymbols(input);

        const items: ModuleQuickPickItem[] = [
            {
                label: '$(arrow-left) Back',
                description: 'Return to main menu',
                action: 'back'
            }
        ];

        // Add matching modules
        if (matchingModules.length > 0) {
            items.push({
                label: `Modules (${matchingModules.length})`,
                kind: vscode.QuickPickItemKind.Separator
            });
            for (const module of matchingModules) {
                items.push({
                    label: `$(file-code) ${module.name}`,
                    description: `${module.category} module`,
                    module: module
                });
            }
        }

        // Add matching symbols
        if (matchingSymbols.length > 0) {
            items.push({
                label: `Operators & Constants (${matchingSymbols.length})`,
                kind: vscode.QuickPickItemKind.Separator
            });
            for (const symbol of matchingSymbols.slice(0, 50)) { // Limit to 50 results
                const icon = symbol.kind === vscode.SymbolKind.Function ? '$(symbol-method)' :
                    symbol.kind === vscode.SymbolKind.Constant ? '$(symbol-constant)' :
                        '$(symbol-variable)';
                items.push({
                    label: `${icon} ${symbol.name}`,
                    description: `from ${symbol.module}`,
                    detail: symbol.documentation?.split('\n')[0],
                    symbol: symbol
                });
            }
        }

        if (items.length === 1) {
            items.push({
                label: '$(search) No results found',
                description: `No modules or operators matching "${input}"`
            });
        }

        const selected = await vscode.window.showQuickPick(items, {
            placeHolder: `Search results for "${input}"`,
            matchOnDescription: true,
            matchOnDetail: true
        });

        if (!selected) {
            return;
        }

        if (selected.action === 'back') {
            await this.showMainMenu();
        } else if (selected.module) {
            await this.showModuleDetails(selected.module);
        } else if (selected.symbol) {
            await this.showSymbolDetails(selected.symbol);
        }
    }

    /**
     * Shows all available operators grouped by module.
     */
    private async showAllOperators(): Promise<void> {
        const allSymbols = await this.symbolProvider.getAllSymbols();
        const operators = allSymbols.filter(s => s.kind === vscode.SymbolKind.Function);

        // Group by module
        const moduleGroups = new Map<string, ModuleSymbol[]>();
        for (const op of operators) {
            const group = moduleGroups.get(op.module) || [];
            group.push(op);
            moduleGroups.set(op.module, group);
        }

        const items: ModuleQuickPickItem[] = [
            {
                label: '$(arrow-left) Back',
                description: 'Return to main menu',
                action: 'back'
            }
        ];

        // Sort modules and add operators
        const sortedModules = Array.from(moduleGroups.keys()).sort();
        for (const moduleName of sortedModules) {
            items.push({
                label: moduleName,
                kind: vscode.QuickPickItemKind.Separator
            });

            const moduleOps = moduleGroups.get(moduleName) || [];
            for (const op of moduleOps.sort((a, b) => a.name.localeCompare(b.name))) {
                const signature = op.arity ? `(${Array(op.arity).fill('_').join(', ')})` : '';
                items.push({
                    label: `$(symbol-method) ${op.name}${signature}`,
                    description: op.documentation?.split('\n')[0],
                    symbol: op
                });
            }
        }

        const selected = await vscode.window.showQuickPick(items, {
            placeHolder: `All Operators (${operators.length} total)`,
            matchOnDescription: true
        });

        if (!selected) {
            return;
        }

        if (selected.action === 'back') {
            await this.showMainMenu();
        } else if (selected.symbol) {
            await this.showSymbolDetails(selected.symbol);
        }
    }

    /**
     * Shows details about a specific symbol.
     */
    private async showSymbolDetails(symbol: ModuleSymbol): Promise<void> {
        const actions = [
            {
                label: '$(add) Insert Symbol',
                description: `Insert "${symbol.name}" at cursor`,
                action: 'insert'
            },
            {
                label: '$(file-code) View Module',
                description: `Open ${symbol.module} module`,
                action: 'view-module'
            },
            {
                label: '$(copy) Copy to Clipboard',
                description: `Copy "${symbol.name}" to clipboard`,
                action: 'copy'
            }
        ];

        const selected = await vscode.window.showQuickPick(actions, {
            placeHolder: `${symbol.name} - ${symbol.module}`
        });

        if (!selected) {
            return;
        }

        switch (selected.action) {
            case 'insert':
                await this.insertSymbol(symbol);
                break;
            case 'view-module': {
                const modules = await this.jarReader.listModules(this.toolsJarPath);
                const module = modules.find(m => m.name === symbol.module);
                if (!module) {
                    const communityModules = await this.jarReader.listModules(this.communityJarPath);
                    const communityModule = communityModules.find(m => m.name === symbol.module);
                    if (communityModule) {
                        await this.viewModuleSource(communityModule);
                    }
                } else {
                    await this.viewModuleSource(module);
                }
                break;
            }
            case 'copy':
                await vscode.env.clipboard.writeText(symbol.name);
                vscode.window.showInformationMessage(`Copied "${symbol.name}" to clipboard`);
                break;
        }
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

    /**
     * Views the source code of a module.
     */
    private async viewModuleSource(module: ModuleInfo): Promise<void> {
        try {
            await this.jarReader.extractModule(module.jarPath, module.internalPath);

            // Create a virtual document
            const uri = vscode.Uri.parse(`tla-module://${module.category}/${module.name}.tla`);
            const doc = await vscode.workspace.openTextDocument(uri);
            await vscode.window.showTextDocument(doc, { preview: true });
        } catch (error) {
            vscode.window.showErrorMessage(`Failed to view module source: ${error}`);
        }
    }

    /**
     * Gets a description for well-known modules.
     */
    private getModuleDescription(moduleName: string): string {
        const descriptions: Record<string, string> = {
            // Standard modules
            'Bags': 'Functions for working with bags (multisets)',
            'FiniteSets': 'Operations on finite sets',
            'Integers': 'Integer arithmetic operations',
            'Naturals': 'Natural number operations',
            'Randomization': 'Random number generation',
            'Reals': 'Real number operations',
            'RealTime': 'Real-time specifications',
            'Sequences': 'Sequence manipulation functions',
            'TLC': 'TLC model checker built-ins',
            'TLCExt': 'Extended TLC functionality',
            'Toolbox': 'Toolbox integration features',
            // Community modules
            'BagsExt': 'Extended bag operations',
            'Bitwise': 'Bitwise operations on integers',
            'CSV': 'CSV file handling',
            'Combinatorics': 'Combinatorial functions',
            'DifferentialEquations': 'Differential equation support',
            'FiniteSetsExt': 'Extended finite set operations',
            'Folds': 'Fold operations for sequences',
            'Functions': 'Function manipulation utilities',
            'Graphs': 'Graph data structure operations',
            'IOUtils': 'Input/output utilities',
            'Json': 'JSON parsing and generation',
            'ShiViz': 'ShiViz visualization support',
            'Statistics': 'Statistical functions'
        };

        return descriptions[moduleName] || 'TLA+ module';
    }
}