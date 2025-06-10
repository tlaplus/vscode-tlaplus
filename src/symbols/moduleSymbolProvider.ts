import * as vscode from 'vscode';
import { runXMLExporter, ToolProcessInfo } from '../tla2tools';
import { XMLParser } from 'fast-xml-parser';
import { ToolOutputChannel } from '../outputChannels';

const symbolsOutChannel = new ToolOutputChannel('TLA+ Module Symbols');

export interface ModuleSymbol {
    name: string;
    module: string;
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

    /**
     * Sets the paths to mega-modules that should be parsed for symbols.
     */
    setMegaModulePaths(paths: string[]): void {
        this.megaModulePaths = paths;
        // Clear cache when paths change
        this.cache.clear();
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

        return this.parseXmlContent(stdoutData);
    }

    /**
     * Parses XML content and extracts module symbols.
     */
    private parseXmlContent(xmlContent: string): ModuleSymbol[] {
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
                    const moduleName = opKind.location?.filename || 'Unknown';

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
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
                    const moduleName = theoremNode.location?.filename || 'Unknown';

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
                            kind: vscode.SymbolKind.Boolean,
                            documentation: `Theorem from ${moduleName}`
                        });
                    }
                } else if (entry.AssumeDef) {
                    const assumeNode = entry.AssumeDef;
                    const name = assumeNode.uniquename;
                    const moduleName = assumeNode.location?.filename || 'Unknown';

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
                            kind: vscode.SymbolKind.Constructor,
                            documentation: `Assumption from ${moduleName}`
                        });
                    }
                } else if (entry.OpDeclNode) {
                    const declNode = entry.OpDeclNode;
                    const name = declNode.uniquename;
                    const moduleName = declNode.location?.filename || 'Unknown';

                    if (name) {
                        symbols.push({
                            name,
                            module: moduleName,
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
        const allSymbols = await this.getAllSymbols();
        return allSymbols.filter(s => s.module === moduleName);
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