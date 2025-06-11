// Make fs operations optional for browser compatibility
type WriteFileFunc = (path: string, data: string, encoding: BufferEncoding) => Promise<void>;
type ReadFileFunc = (path: string, encoding: BufferEncoding) => Promise<string>;
type ExistsFunc = (path: string) => Promise<boolean>;
type PathModule = {
    dirname: (path: string) => string;
    join: (...paths: string[]) => string;
};

let writeFile: WriteFileFunc;
let readFile: ReadFileFunc;
let exists: ExistsFunc;
let path: PathModule;

try {
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const fs = require('fs');
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const pathModule = require('path');
    // eslint-disable-next-line @typescript-eslint/no-var-requires
    const { promisify } = require('util');

    writeFile = promisify(fs.writeFile);
    readFile = promisify(fs.readFile);
    exists = promisify(fs.exists);
    path = pathModule;
} catch {
    // Running in browser context - file operations will not be available
    writeFile = async () => { throw new Error('File operations not available in browser'); };
    readFile = async () => { throw new Error('File operations not available in browser'); };
    exists = async () => false;
    path = { dirname: () => '', join: (...args: string[]) => args.join('/') };
}

export interface SymbolInfo {
    module: string;      // The module that exports this symbol
    kind: 'operator' | 'constant' | 'variable' | 'theorem' | 'assumption';
    isLocal?: boolean;   // Whether this symbol is LOCAL (not exported)
    // Enhanced fields for complete symbol information:
    arity: number;       // Number of parameters (0 for constants/variables)
    parameters?: Array<{name: string; type?: string}>; // Parameter details
    documentation?: string; // Documentation/comments
    level: number;       // Symbol level (1 for basic, 2+ for higher-order)
    location?: {         // Location in source file
        line: number;
        column: number;
    };
}

export interface ModuleRegistryData {
    version: string;
    timestamp: string;
    symbols: {
        [symbolName: string]: SymbolInfo;
    };
    moduleExports: {
        [moduleName: string]: string[];  // List of symbols exported by each module
    };
}

/**
 * Registry that tracks which symbols are exported by which modules.
 * This solves the attribution problem where mega-modules lose track
 * of which module originally exports each symbol.
 */
export class ModuleRegistry {
    private data: ModuleRegistryData = {
        version: '2.0',  // Updated for enhanced symbol information
        timestamp: new Date().toISOString(),
        symbols: {},
        moduleExports: {}
    };

    /**
     * Adds a symbol to the registry with full symbol information.
     */
    addSymbol(
        symbolName: string,
        moduleName: string,
        kind: SymbolInfo['kind'],
        arity: number = 0,
        parameters?: Array<{name: string; type?: string}>,
        documentation?: string,
        level: number = 1,
        isLocal: boolean = false,
        location?: {line: number; column: number}
    ): void {
        // Don't track LOCAL symbols as they're not exported
        if (isLocal) {
            return;
        }

        this.data.symbols[symbolName] = {
            module: moduleName,
            kind,
            isLocal,
            arity,
            parameters,
            documentation,
            level,
            location
        };

        // Add to module exports
        if (!this.data.moduleExports[moduleName]) {
            this.data.moduleExports[moduleName] = [];
        }
        if (!this.data.moduleExports[moduleName].includes(symbolName)) {
            this.data.moduleExports[moduleName].push(symbolName);
        }
    }

    /**
     * Gets the module that exports a given symbol.
     */
    getSymbolModule(symbolName: string): string | undefined {
        return this.data.symbols[symbolName]?.module;
    }

    /**
     * Gets all symbols exported by a module.
     */
    getModuleSymbols(moduleName: string): string[] {
        return this.data.moduleExports[moduleName] || [];
    }

    /**
     * Checks if a symbol exists in the registry.
     */
    hasSymbol(symbolName: string): boolean {
        return symbolName in this.data.symbols;
    }

    /**
     * Saves the registry to a JSON file.
     */
    async save(filePath: string): Promise<void> {
        const dir = path.dirname(filePath);
        if (!await exists(dir)) {
            // eslint-disable-next-line @typescript-eslint/no-var-requires
            const fs = require('fs');
            // eslint-disable-next-line @typescript-eslint/no-var-requires
            const { promisify } = require('util');
            await promisify(fs.mkdir)(dir, { recursive: true });
        }

        const json = JSON.stringify(this.data, null, 2);
        await writeFile(filePath, json, 'utf8');
    }

    /**
     * Loads the registry from a JSON file.
     */
    async load(filePath: string): Promise<boolean> {
        try {
            if (!await exists(filePath)) {
                return false;
            }

            const json = await readFile(filePath, 'utf8');
            this.data = JSON.parse(json);
            return true;
        } catch (error) {
            console.error('Failed to load module registry:', error);
            return false;
        }
    }

    /**
     * Clears the registry.
     */
    clear(): void {
        this.data = {
            version: '2.0',  // Updated for enhanced symbol information
            timestamp: new Date().toISOString(),
            symbols: {},
            moduleExports: {}
        };
    }

    /**
     * Gets the registry data for debugging.
     */
    getData(): ModuleRegistryData {
        return this.data;
    }

    /**
     * Merges another registry into this one.
     */
    merge(other: ModuleRegistry): void {
        const otherData = other.getData();

        // Merge symbols
        Object.assign(this.data.symbols, otherData.symbols);

        // Merge module exports
        for (const [module, symbols] of Object.entries(otherData.moduleExports)) {
            if (!this.data.moduleExports[module]) {
                this.data.moduleExports[module] = [];
            }
            for (const symbol of symbols) {
                if (!this.data.moduleExports[module].includes(symbol)) {
                    this.data.moduleExports[module].push(symbol);
                }
            }
        }
    }
}