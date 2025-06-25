import * as vscode from 'vscode';
import * as path from 'path';
import { ToolOutputChannel } from '../outputChannels';
import { ModuleRegistry } from './moduleRegistry';

const symbolsOutChannel = new ToolOutputChannel('TLA+ Module Symbols');

export interface ModuleSymbol {
    name: string;
    module: string;  // The module where this symbol is defined (e.g., "Sequences")
    kind: vscode.SymbolKind;
    documentation?: string;
    signature?: string;
    level?: number;
    arity?: number;
    parameters?: Array<{name: string; type?: string}>;
}

/**
 * Provides symbols from TLA+ modules for completion and hover information.
 */
export class ModuleSymbolProvider {
    private standardRegistry: ModuleRegistry | null = null;
    private communityRegistry: ModuleRegistry | null = null;
    private cacheDir = '';

    /**
     * Sets the cache directory and loads registries.
     */
    async setCacheDirectory(cacheDir: string): Promise<void> {
        symbolsOutChannel.appendLine('\n=== setCacheDirectory called ===');
        symbolsOutChannel.appendLine(`Cache directory: ${cacheDir}`);

        this.cacheDir = cacheDir;
        // Load registries
        await this.loadRegistries();

        symbolsOutChannel.appendLine('=== END setCacheDirectory ===\n');
    }

    /**
     * Loads the module registries from disk.
     */
    private async loadRegistries(): Promise<void> {
        symbolsOutChannel.appendLine('\n=== loadRegistries called ===');
        try {
            // Load standard modules registry
            const standardPath = path.join(this.cacheDir, 'standard-modules.registry.json');
            symbolsOutChannel.appendLine(`Loading standard registry from: ${standardPath}`);
            this.standardRegistry = new ModuleRegistry();
            const standardLoaded = await this.standardRegistry.load(standardPath);
            symbolsOutChannel.appendLine(`  Standard registry loaded: ${standardLoaded}`);
            if (standardLoaded) {
                const data = this.standardRegistry.getData();
                symbolsOutChannel.appendLine(`  Standard modules: ${Object.keys(data.moduleExports).length}`);
                symbolsOutChannel.appendLine(`  Standard symbols: ${Object.keys(data.symbols).length}`);
            }

            // Load community modules registry
            const communityPath = path.join(this.cacheDir, 'community-modules.registry.json');
            symbolsOutChannel.appendLine(`Loading community registry from: ${communityPath}`);
            this.communityRegistry = new ModuleRegistry();
            const communityLoaded = await this.communityRegistry.load(communityPath);
            symbolsOutChannel.appendLine(`  Community registry loaded: ${communityLoaded}`);
            if (communityLoaded) {
                const data = this.communityRegistry.getData();
                symbolsOutChannel.appendLine(`  Community modules: ${Object.keys(data.moduleExports).length}`);
                symbolsOutChannel.appendLine(`  Community symbols: ${Object.keys(data.symbols).length}`);
            }

            symbolsOutChannel.appendLine('Module registries loaded successfully');
        } catch (error) {
            symbolsOutChannel.appendLine(`Failed to load module registries: ${error}`);
        }
        symbolsOutChannel.appendLine('=== END loadRegistries ===\n');
    }


    /**
     * Gets all available module symbols.
     */
    async getAllSymbols(): Promise<ModuleSymbol[]> {
        symbolsOutChannel.appendLine('\n=== getAllSymbols called ===');

        const allSymbols: ModuleSymbol[] = [];

        // If we don't have registries loaded, return empty array
        if (!this.standardRegistry && !this.communityRegistry) {
            symbolsOutChannel.appendLine('No registries loaded, returning empty array');
            return [];
        }

        // Build symbols directly from registry data
        // This avoids XMLExporter issues with mega-modules that EXTEND modules in JARs

        if (this.standardRegistry) {
            const data = this.standardRegistry.getData();
            symbolsOutChannel.appendLine(
                `Processing ${Object.keys(data.symbols).length} symbols from standard registry`
            );

            for (const [symbolName, symbolInfo] of Object.entries(data.symbols)) {
                // Build documentation from enhanced registry data
                let documentation = symbolInfo.documentation || `From module: ${symbolInfo.module}`;
                if (symbolInfo.level !== undefined) {
                    documentation += `\nLevel: ${this.getLevelName(symbolInfo.level)}`;
                }
                if (symbolInfo.arity && symbolInfo.arity > 0) {
                    documentation += `\nArity: ${symbolInfo.arity}`;
                }
                if (symbolInfo.parameters && symbolInfo.parameters.length > 0) {
                    const paramNames = symbolInfo.parameters.map(p => p.name).join(', ');
                    documentation += `\nParameters: ${paramNames}`;
                }

                // Create a complete ModuleSymbol object with enhanced data
                const symbol: ModuleSymbol = {
                    name: symbolName,
                    module: symbolInfo.module,
                    kind: this.getSymbolKind(symbolInfo.kind),
                    arity: symbolInfo.arity || 0,
                    documentation,
                    level: symbolInfo.level || 1
                };
                allSymbols.push(symbol);
            }
        }

        if (this.communityRegistry) {
            const data = this.communityRegistry.getData();
            symbolsOutChannel.appendLine(
                `Processing ${Object.keys(data.symbols).length} symbols from community registry`
            );

            for (const [symbolName, symbolInfo] of Object.entries(data.symbols)) {
                // Build documentation from enhanced registry data
                let documentation = symbolInfo.documentation || `From module: ${symbolInfo.module}`;
                if (symbolInfo.level !== undefined) {
                    documentation += `\nLevel: ${this.getLevelName(symbolInfo.level)}`;
                }
                if (symbolInfo.arity && symbolInfo.arity > 0) {
                    documentation += `\nArity: ${symbolInfo.arity}`;
                }
                if (symbolInfo.parameters && symbolInfo.parameters.length > 0) {
                    const paramNames = symbolInfo.parameters.map(p => p.name).join(', ');
                    documentation += `\nParameters: ${paramNames}`;
                }

                // Create a complete ModuleSymbol object with enhanced data
                const symbol: ModuleSymbol = {
                    name: symbolName,
                    module: symbolInfo.module,
                    kind: this.getSymbolKind(symbolInfo.kind),
                    arity: symbolInfo.arity || 0,
                    documentation,
                    level: symbolInfo.level || 1
                };
                allSymbols.push(symbol);
            }
        }

        symbolsOutChannel.appendLine(`Total symbols collected: ${allSymbols.length}`);

        // Log sample of symbols for debugging
        if (allSymbols.length > 0) {
            symbolsOutChannel.appendLine('Sample symbols:');
            allSymbols.slice(0, 5).forEach(s => {
                symbolsOutChannel.appendLine(`  - ${s.name} from ${s.module}`);
            });
        }

        symbolsOutChannel.appendLine('=== END getAllSymbols ===\n');

        return allSymbols;
    }







    /**
     * Gets human-readable name for TLA+ level.
     */
    private getLevelName(level: number): string {
        switch (level) {
            case 0: return 'Constant';
            case 1: return 'State';
            case 2: return 'Action';
            case 3: return 'Temporal';
            default: return `Level ${level}`;
        }
    }


    /**
     * Converts a registry kind string to vscode.SymbolKind.
     */
    private getSymbolKind(kind: string): vscode.SymbolKind {
        switch (kind) {
            case 'operator':
                return vscode.SymbolKind.Function;
            case 'constant':
                return vscode.SymbolKind.Constant;
            case 'variable':
                return vscode.SymbolKind.Variable;
            case 'theorem':
                return vscode.SymbolKind.Property;
            case 'assumption':
                return vscode.SymbolKind.Property;
            default:
                return vscode.SymbolKind.Variable;
        }
    }

    /**
     * Gets symbols for a specific module name.
     */
    async getSymbolsForModule(moduleName: string): Promise<ModuleSymbol[]> {
        symbolsOutChannel.appendLine('\n=== getSymbolsForModule ===');
        symbolsOutChannel.appendLine(`Requested module: "${moduleName}"`);

        // Use the registry to get symbols that are exported by the requested module
        const exportedSymbols: ModuleSymbol[] = [];

        // Check standard registry
        if (this.standardRegistry) {
            const standardSymbolNames = this.standardRegistry.getModuleSymbols(moduleName);
            symbolsOutChannel.appendLine(
                `Found ${standardSymbolNames.length} symbols in standard registry for ${moduleName}`
            );

            const data = this.standardRegistry.getData();
            for (const symbolName of standardSymbolNames) {
                const symbolInfo = data.symbols[symbolName];
                if (symbolInfo) {
                    // Build documentation from enhanced registry data
                    let documentation = symbolInfo.documentation || `From module: ${moduleName}`;
                    if (symbolInfo.level !== undefined) {
                        documentation += `\nLevel: ${this.getLevelName(symbolInfo.level)}`;
                    }
                    if (symbolInfo.arity && symbolInfo.arity > 0) {
                        documentation += `\nArity: ${symbolInfo.arity}`;
                    }
                    if (symbolInfo.parameters && symbolInfo.parameters.length > 0) {
                        const paramNames = symbolInfo.parameters.map(p => p.name).join(', ');
                        documentation += `\nParameters: ${paramNames}`;
                    }

                    exportedSymbols.push({
                        name: symbolName,
                        module: moduleName,
                        kind: this.getSymbolKind(symbolInfo.kind),
                        arity: symbolInfo.arity || 0,
                        documentation,
                        level: symbolInfo.level || 1
                    });
                }
            }
        }

        // Check community registry
        if (this.communityRegistry) {
            const communitySymbolNames = this.communityRegistry.getModuleSymbols(moduleName);
            symbolsOutChannel.appendLine(
                `Found ${communitySymbolNames.length} symbols in community registry for ${moduleName}`
            );

            const data = this.communityRegistry.getData();
            for (const symbolName of communitySymbolNames) {
                const symbolInfo = data.symbols[symbolName];
                if (symbolInfo) {
                    // Build documentation from enhanced registry data
                    let documentation = symbolInfo.documentation || `From module: ${moduleName}`;
                    if (symbolInfo.level !== undefined) {
                        documentation += `\nLevel: ${this.getLevelName(symbolInfo.level)}`;
                    }
                    if (symbolInfo.arity && symbolInfo.arity > 0) {
                        documentation += `\nArity: ${symbolInfo.arity}`;
                    }
                    if (symbolInfo.parameters && symbolInfo.parameters.length > 0) {
                        const paramNames = symbolInfo.parameters.map(p => p.name).join(', ');
                        documentation += `\nParameters: ${paramNames}`;
                    }

                    exportedSymbols.push({
                        name: symbolName,
                        module: moduleName,
                        kind: this.getSymbolKind(symbolInfo.kind),
                        arity: symbolInfo.arity || 0,
                        documentation,
                        level: symbolInfo.level || 1
                    });
                }
            }
        }

        symbolsOutChannel.appendLine(`Returning ${exportedSymbols.length} symbols for ${moduleName}`);
        symbolsOutChannel.appendLine('=== END getSymbolsForModule ===\n');

        return exportedSymbols;
    }

    /**
     * Searches for symbols by name pattern.
     */
    async searchSymbols(pattern: string): Promise<ModuleSymbol[]> {
        const allSymbols = await this.getAllSymbols();
        const lowerPattern = pattern.toLowerCase();

        return allSymbols.filter(s =>
            s.name.toLowerCase().includes(lowerPattern)
        );
    }
}