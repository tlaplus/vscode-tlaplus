import * as vscode from 'vscode';
import * as path from 'path';
import { runXMLExporter, ToolProcessInfo } from '../tla2tools';
import { XMLParser } from 'fast-xml-parser';
import { ToolOutputChannel } from '../outputChannels';
import { ModuleRegistry } from './moduleRegistry';

const symbolsOutChannel = new ToolOutputChannel('TLA+ Module Symbols');

export interface ModuleSymbol {
    name: string;
    module: string;  // The module where this symbol is defined (e.g., "Sequences")
    sourceModule?: string;  // The mega-module file this was parsed from (e.g., "Json")
    kind: vscode.SymbolKind;
    documentation?: string;
    signature?: string;
    level?: number;
    arity?: number;
}

interface SymbolCache {
    symbols: ModuleSymbol[];
    timestamp: number;
}

/**
 * Provides symbols from TLA+ modules for completion and hover information.
 */
export class ModuleSymbolProvider {
    private cache = new Map<string, SymbolCache>();
    private readonly CACHE_TTL = 300000; // 5 minutes
    private megaModulePaths: string[] = [];
    private moduleToMegaModule = new Map<string, string>();
    private standardRegistry: ModuleRegistry | null = null;
    private communityRegistry: ModuleRegistry | null = null;
    private cacheDir = '';

    /**
     * Sets the paths to mega-modules that should be parsed for symbols.
     */
    setMegaModulePaths(paths: string[], cacheDir: string): void {
        this.megaModulePaths = paths;
        this.cacheDir = cacheDir;
        // Clear cache when paths change
        this.cache.clear();
        // Load registries
        this.loadRegistries();
    }

    /**
     * Loads the module registries from disk.
     */
    private async loadRegistries(): Promise<void> {
        try {
            // Load standard modules registry
            const standardPath = path.join(this.cacheDir, 'standard-modules.registry.json');
            this.standardRegistry = new ModuleRegistry();
            await this.standardRegistry.load(standardPath);

            // Load community modules registry
            const communityPath = path.join(this.cacheDir, 'community-modules.registry.json');
            this.communityRegistry = new ModuleRegistry();
            await this.communityRegistry.load(communityPath);

            symbolsOutChannel.appendLine('Module registries loaded successfully');
        } catch (error) {
            symbolsOutChannel.appendLine(`Failed to load module registries: ${error}`);
        }
    }

    /**
     * Gets all available module symbols.
     */
    async getAllSymbols(): Promise<ModuleSymbol[]> {
        const allSymbols: ModuleSymbol[] = [];

        for (const modulePath of this.megaModulePaths) {
            const symbols = await this.getModuleSymbols(modulePath);
            allSymbols.push(...symbols);
        }

        return allSymbols;
    }

    /**
     * Gets symbols from a specific module.
     */
    async getModuleSymbols(modulePath: string): Promise<ModuleSymbol[]> {
        // Check cache first
        const cached = this.cache.get(modulePath);
        if (cached && Date.now() - cached.timestamp < this.CACHE_TTL) {
            return cached.symbols;
        }

        try {
            const symbols = await this.parseModuleSymbols(modulePath);

            // Cache the results
            this.cache.set(modulePath, {
                symbols,
                timestamp: Date.now()
            });

            return symbols;
        } catch (error) {
            symbolsOutChannel.appendLine(`Failed to parse symbols from ${modulePath}: ${error}`);
            return [];
        }
    }

    /**
     * Parses symbols from a TLA+ module using the XML exporter.
     */
    private async parseModuleSymbols(modulePath: string): Promise<ModuleSymbol[]> {
        const processInfo: ToolProcessInfo = await runXMLExporter(modulePath, false);

        // Extract module name from file path (e.g., "/path/to/Json.tla" -> "Json")
        const path = await import('path');
        const moduleBasename = path.basename(modulePath, path.extname(modulePath));


        // Collect stdout
        let stdoutData = '';
        processInfo.process.stdout?.on('data', (data) => {
            stdoutData += data.toString();
        });

        // Collect stderr for debugging
        let stderrData = '';
        processInfo.process.stderr?.on('data', (data) => {
            stderrData += data.toString();
        });

        // Wait for process to complete
        const exitCode = await new Promise<number>((resolve) => {
            processInfo.process.on('close', (code) => {
                resolve(code ?? 1);
            });
        });

        if (exitCode !== 0) {
            throw new Error(`XML exporter failed with exit code ${exitCode}: ${stderrData}`);
        }

        if (!stdoutData) {
            throw new Error('XML exporter produced no output');
        }

        return this.parseXmlContent(stdoutData, moduleBasename);
    }

    /**
     * Normalizes a module name by removing the .tla extension if present.
     */
    private normalizeModuleName(name: string): string {
        if (name.endsWith('.tla')) {
            return name.slice(0, -4);
        }
        return name;
    }

    /**
     * Parses XML content and extracts module symbols.
     */
    private parseXmlContent(xmlContent: string, sourceModuleName: string): ModuleSymbol[] {
        const symbols: ModuleSymbol[] = [];

        try {
            const parser = new XMLParser({
                ignoreAttributes: false,
                attributeNamePrefix: '',
                isArray: (name) => ['entry', 'ModuleNodeRef', 'operands', 'params'].includes(name)
            });

            const xmlObj = parser.parse(xmlContent);
            if (!xmlObj.modules || !xmlObj.modules.context || !xmlObj.modules.context.entry) {
                return symbols;
            }

            // Process all entries

            for (const entry of xmlObj.modules.context.entry) {
                if (entry.UserDefinedOpKind) {
                    const opKind = entry.UserDefinedOpKind;
                    const name = opKind.uniquename;
                    const rawModuleName = opKind.location?.filename || 'Unknown';
                    const moduleName = this.normalizeModuleName(rawModuleName);

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
                            sourceModule: sourceModuleName,
                            kind: this.determineSymbolKind(
                                parseInt(opKind.level || '0'),
                                parseInt(opKind.arity || '0')
                            ),
                            level: parseInt(opKind.level || '0'),
                            arity: parseInt(opKind.arity || '0'),
                            documentation: this.generateDocumentation(name, moduleName, opKind)
                        });
                    }
                } else if (entry.TheoremDefNode) {
                    const theoremNode = entry.TheoremDefNode;
                    const name = theoremNode.uniquename;
                    const rawModuleName = theoremNode.location?.filename || 'Unknown';
                    const moduleName = this.normalizeModuleName(rawModuleName);

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
                            sourceModule: sourceModuleName,
                            kind: vscode.SymbolKind.Boolean,
                            documentation: `Theorem from ${moduleName}`
                        });
                    }
                } else if (entry.AssumeDef) {
                    const assumeNode = entry.AssumeDef;
                    const name = assumeNode.uniquename;
                    const rawModuleName = assumeNode.location?.filename || 'Unknown';
                    const moduleName = this.normalizeModuleName(rawModuleName);

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
                            sourceModule: sourceModuleName,
                            kind: vscode.SymbolKind.Constructor,
                            documentation: `Assumption from ${moduleName}`
                        });
                    }
                } else if (entry.OpDeclNode) {
                    const declNode = entry.OpDeclNode;
                    const name = declNode.uniquename;
                    const rawModuleName = declNode.location?.filename || 'Unknown';
                    const moduleName = this.normalizeModuleName(rawModuleName);

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
                            sourceModule: sourceModuleName,
                            kind: this.determineSymbolKind(
                                parseInt(declNode.level || '0'),
                                parseInt(declNode.arity || '0')
                            ),
                            level: parseInt(declNode.level || '0'),
                            arity: parseInt(declNode.arity || '0'),
                            documentation: this.generateDocumentation(name, moduleName, declNode)
                        });
                    }
                }
            }

            return symbols;
        } catch (error) {
            symbolsOutChannel.appendLine(`Failed to parse XML: ${error}`);
            return symbols;
        }
    }

    /**
     * Determines the appropriate SymbolKind based on TLA+ level and arity.
     */
    private determineSymbolKind(level: number, arity: number): vscode.SymbolKind {
        if (level === 0) {
            return vscode.SymbolKind.Constant;
        } else if (arity > 0) {
            return vscode.SymbolKind.Function;
        } else {
            return vscode.SymbolKind.Variable;
        }
    }

    /**
     * Generates documentation for a symbol.
     */
    private generateDocumentation(name: string, module: string, node: {
        level?: string;
        kind?: string;
        params?: string | { name: string }[];
        arity?: string;
    }): string {
        let doc = `From module: ${module}\n`;

        if (node.level !== undefined) {
            const levelName = this.getLevelName(parseInt(node.level));
            doc += `Level: ${levelName}\n`;
        }

        if (node.arity !== undefined && parseInt(node.arity) > 0) {
            doc += `Arity: ${node.arity}\n`;
        }

        return doc;
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
     * Clears the symbol cache.
     */
    clearCache(): void {
        this.cache.clear();
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

            if (standardSymbolNames.length > 0) {
                // Get all parsed symbols from mega-modules
                const allSymbols = await this.getAllSymbols();

                // Find the actual symbol objects for the exported names
                for (const symbolName of standardSymbolNames) {
                    const symbol = allSymbols.find(s => s.name === symbolName);
                    if (symbol) {
                        // Create a new symbol with corrected module attribution
                        exportedSymbols.push({
                            ...symbol,
                            module: moduleName  // Override to show it as coming from the requested module
                        });
                    }
                }
            }
        }

        // Check community registry
        if (this.communityRegistry) {
            const communitySymbolNames = this.communityRegistry.getModuleSymbols(moduleName);
            symbolsOutChannel.appendLine(
                `Found ${communitySymbolNames.length} symbols in community registry for ${moduleName}`
            );

            if (communitySymbolNames.length > 0) {
                // Get all parsed symbols from mega-modules
                const allSymbols = await this.getAllSymbols();

                // Find the actual symbol objects for the exported names
                for (const symbolName of communitySymbolNames) {
                    const symbol = allSymbols.find(s => s.name === symbolName);
                    if (symbol) {
                        // Create a new symbol with corrected module attribution
                        exportedSymbols.push({
                            ...symbol,
                            module: moduleName  // Override to show it as coming from the requested module
                        });
                    }
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