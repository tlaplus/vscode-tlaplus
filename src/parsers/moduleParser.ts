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

            // Add symbols to registry with enhanced information
            let addedCount = 0;
            for (const symbol of definedSymbols) {
                registry.addSymbol(
                    symbol.name,
                    moduleName,
                    symbol.kind,
                    symbol.arity,
                    symbol.parameters,
                    symbol.documentation,
                    symbol.level,
                    symbol.isLocal,
                    symbol.location
                );
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
     * Extracts symbols defined in the module content with full information.
     */
    private extractDefinedSymbols(content: string, moduleName: string): Array<{
        name: string;
        kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption';
        arity: number;
        parameters?: Array<{name: string; type?: string}>;
        documentation?: string;
        level: number;
        isLocal: boolean;
        location?: {line: number; column: number};
    }> {
        const symbols: Array<{
            name: string;
            kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption';
            arity: number;
            parameters?: Array<{name: string; type?: string}>;
            documentation?: string;
            level: number;
            isLocal: boolean;
            location?: {line: number; column: number};
        }> = [];

        // Keep track of line numbers for location info
        const lines = content.split('\n');

        // Extract operators with full information
        const operatorRegex = /^(\s*)(LOCAL\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(([^)]*)\))?\s*==(?!=)/gm;
        let match;
        while ((match = operatorRegex.exec(content)) !== null) {
            const indent = match[1];
            const isLocal = !!match[2];
            const name = match[3];
            const paramsStr = match[4];

            if (!this.isBuiltInOperator(name) && !name.startsWith('_')) {
                // Calculate line number
                const upToMatch = content.substring(0, match.index);
                const lineNumber = upToMatch.split('\n').length;
                const columnNumber = indent.length + 1;

                // Extract parameters
                const parameters: Array<{name: string; type?: string}> = [];
                let arity = 0;
                if (paramsStr) {
                    const params = paramsStr.split(',').map(p => p.trim()).filter(p => p);
                    arity = params.length;
                    for (const param of params) {
                        parameters.push({ name: param });
                    }
                }

                // Extract documentation (look for comments above the definition)
                const documentation = this.extractDocumentation(lines, lineNumber - 1);

                symbols.push({
                    name,
                    kind: 'operator',
                    arity,
                    parameters: parameters.length > 0 ? parameters : undefined,
                    documentation,
                    level: 1, // Basic level, could be enhanced with more analysis
                    isLocal,
                    location: { line: lineNumber, column: columnNumber }
                });
            }
        }

        // Extract constants (CONSTANT declarations)
        const constantRegex = /^(\s*)(LOCAL\s+)?CONSTANT(?:S)?\s+([A-Za-z_][A-Za-z0-9_,\s]*)/gm;
        while ((match = constantRegex.exec(content)) !== null) {
            const indent = match[1];
            const isLocal = !!match[2];
            const names = match[3].split(',').map(n => n.trim()).filter(n => n);

            const upToMatch = content.substring(0, match.index);
            const lineNumber = upToMatch.split('\n').length;
            const columnNumber = indent.length + 1;
            const documentation = this.extractDocumentation(lines, lineNumber - 1);

            for (const name of names) {
                if (!this.isBuiltInOperator(name)) {
                    symbols.push({
                        name,
                        kind: 'constant',
                        arity: 0,
                        documentation,
                        level: 0,
                        isLocal,
                        location: { line: lineNumber, column: columnNumber }
                    });
                }
            }
        }

        // Extract variables (VARIABLE declarations)
        const variableRegex = /^(\s*)(LOCAL\s+)?VARIABLE(?:S)?\s+([A-Za-z_][A-Za-z0-9_,\s]*)/gm;
        while ((match = variableRegex.exec(content)) !== null) {
            const indent = match[1];
            const isLocal = !!match[2];
            const names = match[3].split(',').map(n => n.trim()).filter(n => n);

            const upToMatch = content.substring(0, match.index);
            const lineNumber = upToMatch.split('\n').length;
            const columnNumber = indent.length + 1;
            const documentation = this.extractDocumentation(lines, lineNumber - 1);

            for (const name of names) {
                if (!this.isBuiltInOperator(name)) {
                    symbols.push({
                        name,
                        kind: 'variable',
                        arity: 0,
                        documentation,
                        level: 1,
                        isLocal,
                        location: { line: lineNumber, column: columnNumber }
                    });
                }
            }
        }

        // Extract theorems
        const theoremRegex = /^(\s*)(LOCAL\s+)?THEOREM\s+([A-Za-z_][A-Za-z0-9_]*)\s*==/gm;
        while ((match = theoremRegex.exec(content)) !== null) {
            const indent = match[1];
            const isLocal = !!match[2];
            const name = match[3];

            const upToMatch = content.substring(0, match.index);
            const lineNumber = upToMatch.split('\n').length;
            const columnNumber = indent.length + 1;
            const documentation = this.extractDocumentation(lines, lineNumber - 1);

            symbols.push({
                name,
                kind: 'theorem',
                arity: 0,
                documentation,
                level: 1,
                isLocal,
                location: { line: lineNumber, column: columnNumber }
            });
        }

        // Extract assumptions
        const assumeRegex = /^(\s*)(LOCAL\s+)?ASSUME\s+([A-Za-z_][A-Za-z0-9_]*)\s*==/gm;
        while ((match = assumeRegex.exec(content)) !== null) {
            const indent = match[1];
            const isLocal = !!match[2];
            const name = match[3];

            const upToMatch = content.substring(0, match.index);
            const lineNumber = upToMatch.split('\n').length;
            const columnNumber = indent.length + 1;
            const documentation = this.extractDocumentation(lines, lineNumber - 1);

            symbols.push({
                name,
                kind: 'assumption',
                arity: 0,
                documentation,
                level: 1,
                isLocal,
                location: { line: lineNumber, column: columnNumber }
            });
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

    /**
     * Extracts documentation from comments above a symbol definition.
     */
    private extractDocumentation(lines: string[], startLine: number): string | undefined {
        const docs: string[] = [];

        // Look backwards from the line above the definition
        for (let i = startLine; i >= 0; i--) {
            const line = lines[i].trim();

            // Stop if we hit a non-comment line
            if (line && !line.startsWith('\\*') && !line.includes('(*')) {
                break;
            }

            // Extract line comment
            const lineCommentMatch = line.match(/\\\*\s*(.*?)\s*\*\\/);
            if (lineCommentMatch) {
                docs.unshift(lineCommentMatch[1]);
                continue;
            }

            // Extract from block comment
            const blockCommentMatch = line.match(/\(\*\s*(.*?)\s*\*\)/);
            if (blockCommentMatch) {
                docs.unshift(blockCommentMatch[1]);
                continue;
            }

            // Handle multi-line block comments (simplified)
            if (line.includes('*)')) {
                // End of block comment
                const content = line.substring(0, line.indexOf('*)')).trim();
                if (content) {
                    docs.unshift(content);
                }
            } else if (line.includes('(*')) {
                // Start of block comment
                const content = line.substring(line.indexOf('(*') + 2).trim();
                if (content) {
                    docs.unshift(content);
                }
                break;
            } else if (i < startLine && line.startsWith('*')) {
                // Inside block comment
                docs.unshift(line.substring(1).trim());
            }
        }

        return docs.length > 0 ? docs.join(' ') : undefined;
    }
}
