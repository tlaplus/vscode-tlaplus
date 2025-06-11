import { ModuleRegistry } from '../symbols/moduleRegistry';
import { ToolOutputChannel } from '../outputChannels';
import { runXMLExporter, ToolProcessInfo } from '../tla2tools';
import { XMLParser } from 'fast-xml-parser';

const parserChannel = new ToolOutputChannel('TLA+ Module Parser');

/**
 * Parses individual TLA+ modules to extract symbol information.
 * This is used during mega-module generation to build the symbol registry.
 */
export class ModuleParser {
    private xmlParser: XMLParser;

    constructor() {
        this.xmlParser = new XMLParser({
            ignoreAttributes: false,
            attributeNamePrefix: '',
            isArray: (name) => ['entry', 'ModuleNodeRef', 'operands', 'params'].includes(name)
        });
    }

    /**
     * Parses a single TLA+ module and adds its symbols to the registry.
     * For now, we'll use a simpler approach - parse the module content directly
     * to extract what symbols it defines, not what it imports.
     */
    async parseModule(moduleContent: string, moduleName: string, registry: ModuleRegistry): Promise<void> {
        parserChannel.appendLine(`\nParsing module: ${moduleName}`);

        try {
            // Extract module structure
            const localInstances = this.extractLocalInstances(moduleContent);
            const publicInstances = this.extractPublicInstances(moduleContent);
            const extendsModules = this.extractExtends(moduleContent);

            parserChannel.appendLine(`  LOCAL INSTANCE: ${localInstances.join(', ') || 'none'}`);
            parserChannel.appendLine(`  INSTANCE: ${publicInstances.join(', ') || 'none'}`);
            parserChannel.appendLine(`  EXTENDS: ${extendsModules.join(', ') || 'none'}`);

            // Extract symbols defined in this module
            const definedSymbols = this.extractDefinedSymbols(moduleContent, moduleName);

            // Add symbols to registry
            let addedCount = 0;
            for (const symbol of definedSymbols) {
                registry.addSymbol(symbol.name, moduleName, symbol.kind);
                addedCount++;
            }

            parserChannel.appendLine(`  Added ${addedCount} symbols to registry for ${moduleName}`);

        } catch (error) {
            parserChannel.appendLine(`  ERROR parsing ${moduleName}: ${error}`);
        }
    }

    /**
     * Reads module content from JAR or file.
     */
    private async readModuleContent(modulePath: string): Promise<string> {
        // For now, we'll use a simple approach - this needs to be enhanced
        // to read from JAR files properly
        const fs = await import('fs');
        const { promisify } = await import('util');

        try {
            const content = await promisify(fs.readFile)(modulePath, 'utf8');
            return content;
        } catch {
            // If direct file read fails, we need to extract from JAR
            // This is a placeholder - needs proper JAR reading
            return '';
        }
    }

    /**
     * Extracts LOCAL INSTANCE declarations from module content.
     */
    private extractLocalInstances(content: string): string[] {
        const instances: string[] = [];
        const regex = /LOCAL\s+INSTANCE\s+(\w+)/g;
        let match;

        while ((match = regex.exec(content)) !== null) {
            instances.push(match[1]);
        }

        return instances;
    }

    /**
     * Extracts public INSTANCE declarations from module content.
     */
    private extractPublicInstances(content: string): string[] {
        const instances: string[] = [];
        // Match INSTANCE but not LOCAL INSTANCE
        const regex = /(?<!LOCAL\s)INSTANCE\s+(\w+)/g;
        let match;

        while ((match = regex.exec(content)) !== null) {
            instances.push(match[1]);
        }

        return instances;
    }

    /**
     * Extracts EXTENDS declarations from module content.
     */
    private extractExtends(content: string): string[] {
        const modules: string[] = [];
        const regex = /EXTENDS\s+([^-\n]+)/g;
        let match;

        while ((match = regex.exec(content)) !== null) {
            // Split by comma and clean up
            const moduleList = match[1].split(',').map(m => m.trim()).filter(m => m);
            modules.push(...moduleList);
        }

        return modules;
    }

    /**
     * Runs XMLExporter on a module and returns the XML output.
     */
    private async runXMLExporter(modulePath: string): Promise<string | null> {
        try {
            const processInfo: ToolProcessInfo = await runXMLExporter(modulePath, false);

            let xmlOutput = '';
            processInfo.process.stdout?.on('data', (data) => {
                xmlOutput += data.toString();
            });

            let stderrOutput = '';
            processInfo.process.stderr?.on('data', (data) => {
                stderrOutput += data.toString();
            });

            const exitCode = await new Promise<number>((resolve) => {
                processInfo.process.on('close', (code) => {
                    resolve(code ?? 1);
                });
            });

            if (exitCode !== 0) {
                parserChannel.appendLine(`  XMLExporter failed: ${stderrOutput}`);
                return null;
            }

            return xmlOutput;
        } catch (error) {
            parserChannel.appendLine(`  XMLExporter error: ${error}`);
            return null;
        }
    }

    /**
     * Extracts symbols from XML output.
     */
    private extractSymbolsFromXML(xmlContent: string, moduleName: string): Array<{
        name: string;
        definedIn: string;
        kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption';
    }> {
        const symbols: Array<{
            name: string;
            definedIn: string;
            kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption';
        }> = [];

        try {
            const xmlObj = this.xmlParser.parse(xmlContent);
            if (!xmlObj.modules || !xmlObj.modules.context || !xmlObj.modules.context.entry) {
                return symbols;
            }

            for (const entry of xmlObj.modules.context.entry) {
                let name: string | undefined;
                let definedIn: string | undefined;
                let kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption' = 'operator';

                if (entry.UserDefinedOpKind) {
                    name = entry.UserDefinedOpKind.uniquename;
                    definedIn = this.extractModuleName(entry.UserDefinedOpKind.location?.filename);
                    kind = this.determineKind(entry.UserDefinedOpKind);
                } else if (entry.OpDeclNode) {
                    name = entry.OpDeclNode.uniquename;
                    definedIn = this.extractModuleName(entry.OpDeclNode.location?.filename);
                    kind = this.determineKind(entry.OpDeclNode);
                } else if (entry.TheoremDefNode) {
                    name = entry.TheoremDefNode.uniquename;
                    definedIn = this.extractModuleName(entry.TheoremDefNode.location?.filename);
                    kind = 'theorem';
                } else if (entry.AssumeDef) {
                    name = entry.AssumeDef.uniquename;
                    definedIn = this.extractModuleName(entry.AssumeDef.location?.filename);
                    kind = 'assumption';
                }

                if (name && definedIn) {
                    symbols.push({ name, definedIn, kind });
                }
            }

            return symbols;
        } catch (error) {
            parserChannel.appendLine(`  XML parse error: ${error}`);
            return symbols;
        }
    }

    /**
     * Extracts module name from filename.
     */
    private extractModuleName(filename: string | undefined): string {
        if (!filename) {return 'Unknown';}

        // Remove .tla extension
        if (filename.endsWith('.tla')) {
            filename = filename.slice(0, -4);
        }

        // Extract just the module name (no path)
        const parts = filename.split(/[/\\]/);
        return parts[parts.length - 1];
    }

    /**
     * Determines the kind of symbol from XML node.
     */
    private determineKind(node: {level?: string; arity?: string}): 'operator' | 'constant' | 'variable' {
        const level = parseInt(node.level || '0');
        const arity = parseInt(node.arity || '0');

        if (level === 0) {
            return 'constant';
        } else if (arity > 0) {
            return 'operator';
        } else {
            return 'variable';
        }
    }

    /**
     * Checks if a symbol is a built-in operator.
     */
    private isBuiltInOperator(name: string): boolean {
        // Built-in operators that are available everywhere
        const builtIns = [
            // Logic
            'TRUE', 'FALSE', 'BOOLEAN', '~', '/\\', '\\/', '=>', '<=>',
            // Equality
            '=', '#', '/=',
            // Sets
            'SUBSET', 'UNION', 'DOMAIN',
            // Functions
            'CHOOSE', 'ENABLED', 'UNCHANGED',
            // Temporal
            '[]', '<>', '~>', '-+->',
            // Other
            'EXCEPT', 'LET', 'IN'
        ];

        return builtIns.includes(name);
    }

    /**
     * Extracts symbols defined in the module content.
     */
    private extractDefinedSymbols(content: string, moduleName: string): Array<{
        name: string;
        kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption';
    }> {
        const symbols: Array<{
            name: string;
            kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption';
        }> = [];

        // Remove comments
        const cleanContent = this.removeComments(content);

        // Extract operators (name == definition or name(params) == definition)
        const operatorRegex = /^\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:\([^)]*\))?\s*==(?!=)/gm;
        let match;
        while ((match = operatorRegex.exec(cleanContent)) !== null) {
            const name = match[1];
            if (!this.isBuiltInOperator(name) && !name.startsWith('_')) {
                symbols.push({ name, kind: 'operator' });
            }
        }

        // Extract constants (CONSTANT declarations)
        const constantRegex = /^\s*CONSTANT(?:S)?\s+([A-Za-z_][A-Za-z0-9_,\s]*)/gm;
        while ((match = constantRegex.exec(cleanContent)) !== null) {
            const names = match[1].split(',').map(n => n.trim()).filter(n => n);
            for (const name of names) {
                if (!this.isBuiltInOperator(name)) {
                    symbols.push({ name, kind: 'constant' });
                }
            }
        }

        // Extract variables (VARIABLE declarations)
        const variableRegex = /^\s*VARIABLE(?:S)?\s+([A-Za-z_][A-Za-z0-9_,\s]*)/gm;
        while ((match = variableRegex.exec(cleanContent)) !== null) {
            const names = match[1].split(',').map(n => n.trim()).filter(n => n);
            for (const name of names) {
                if (!this.isBuiltInOperator(name)) {
                    symbols.push({ name, kind: 'variable' });
                }
            }
        }

        // Extract theorems
        const theoremRegex = /^\s*THEOREM\s+([A-Za-z_][A-Za-z0-9_]*)\s*==/gm;
        while ((match = theoremRegex.exec(cleanContent)) !== null) {
            symbols.push({ name: match[1], kind: 'theorem' });
        }

        // Extract assumptions
        const assumeRegex = /^\s*ASSUME\s+([A-Za-z_][A-Za-z0-9_]*)\s*==/gm;
        while ((match = assumeRegex.exec(cleanContent)) !== null) {
            symbols.push({ name: match[1], kind: 'assumption' });
        }

        return symbols;
    }

    /**
     * Removes comments from TLA+ content.
     */
    private removeComments(content: string): string {
        // Remove line comments (\* ... *)
        content = content.replace(/\\\*[^\n]*\*\\/g, '');

        // Remove block comments (* ... *) - simple version
        content = content.replace(/\(\*[\s\S]*?\*\)/g, '');

        return content;
    }
}