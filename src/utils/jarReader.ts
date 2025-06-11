import * as yauzl from 'yauzl';
import * as path from 'path';

export interface ModuleInfo {
    name: string;
    jarPath: string;
    internalPath: string;
    category: 'standard' | 'community' | 'tlaps';
    lastModified: number;
}

export interface JarReader {
    listModules(jarPath: string): Promise<ModuleInfo[]>;
    extractModule(jarPath: string, modulePath: string): Promise<string>;
    extractModuleContent(jarPath: string, modulePath: string): Promise<string>;
}

/**
 * Reads TLA+ modules from JAR files.
 */
export class JarModuleReader implements JarReader {
    private cache = new Map<string, { modules: ModuleInfo[], timestamp: number }>();
    private readonly CACHE_TTL = 60000; // 1 minute cache

    /**
     * Lists all TLA+ modules in a JAR file.
     */
    async listModules(jarPath: string): Promise<ModuleInfo[]> {
        // Check cache first
        const cached = this.cache.get(jarPath);
        if (cached && Date.now() - cached.timestamp < this.CACHE_TTL) {
            return cached.modules;
        }

        const modules: ModuleInfo[] = [];
        const category = this.getCategory(jarPath);

        return new Promise((resolve, reject) => {
            yauzl.open(jarPath, { lazyEntries: true }, (err, zipfile) => {
                if (err) {
                    reject(err);
                    return;
                }

                zipfile.readEntry();
                zipfile.on('entry', (entry: yauzl.Entry) => {
                    const entryPath = entry.fileName;

                    // Check if this is a TLA+ module
                    if (entryPath.endsWith('.tla') && !entryPath.includes('__MACOSX')) {
                        // Skip internal modules
                        const moduleName = path.basename(entryPath, '.tla');
                        if (!this.isInternalModule(moduleName)) {
                            modules.push({
                                name: moduleName,
                                jarPath: jarPath,
                                internalPath: entryPath,
                                category: category,
                                lastModified: Date.now() // yauzl Entry doesn't expose lastModified
                            });
                        }
                    }

                    zipfile.readEntry();
                });

                zipfile.on('end', () => {
                    // Cache the results
                    this.cache.set(jarPath, { modules, timestamp: Date.now() });
                    resolve(modules);
                });

                zipfile.on('error', reject);
            });
        });
    }

    /**
     * Extracts the content of a specific module from a JAR file.
     */
    async extractModule(jarPath: string, modulePath: string): Promise<string> {
        return new Promise((resolve, reject) => {
            yauzl.open(jarPath, { lazyEntries: true }, (err, zipfile) => {
                if (err) {
                    reject(err);
                    return;
                }

                zipfile.readEntry();
                zipfile.on('entry', (entry: yauzl.Entry) => {
                    if (entry.fileName === modulePath) {
                        zipfile.openReadStream(entry, (err, readStream) => {
                            if (err) {
                                zipfile.close(); // Ensure zipfile is closed on error
                                reject(err);
                                return;
                            }

                            const chunks: Buffer[] = [];
                            readStream.on('data', (chunk: Buffer) => chunks.push(chunk));
                            readStream.on('end', () => {
                                const content = Buffer.concat(chunks).toString('utf8');
                                zipfile.close(); // Ensure zipfile is closed after resolving
                                resolve(content);
                            });
                            readStream.on('error', (err) => {
                                zipfile.close(); // Ensure zipfile is closed on error
                                reject(err);
                            });
                        });
                    } else {
                        zipfile.readEntry();
                    }
                });

                zipfile.on('end', () => {
                    zipfile.close(); // Ensure zipfile is closed when not found
                    reject(new Error(`Module ${modulePath} not found in ${jarPath}`));
                });

                zipfile.on('error', (err) => {
                    zipfile.close(); // Ensure zipfile is closed on error
                    reject(err);
                });
            });
        });
    }

    /**
     * Determines the category based on the JAR file name.
     */
    private getCategory(jarPath: string): 'standard' | 'community' | 'tlaps' {
        const fileName = path.basename(jarPath);
        if (fileName.includes('tla2tools')) {
            return 'standard';
        } else if (fileName.includes('CommunityModules')) {
            return 'community';
        } else if (fileName.includes('tlaps')) {
            return 'tlaps';
        }
        return 'standard'; // Default fallback
    }

    /**
     * Checks if a module is internal and should be excluded.
     */
    private isInternalModule(moduleName: string): boolean {
        const internalModules = [
            'MC', 'MCAliases', 'MCRealTime', 'TESpecTest', 'TETrace',
            '_JsonTrace', '_TLAPlusCounterExample', '_TLAPlusDebugger', 'SubsetValue'
        ];
        return internalModules.includes(moduleName) || moduleName.startsWith('_');
    }

    /**
     * Alias for extractModule - extracts module content from JAR.
     */
    async extractModuleContent(jarPath: string, modulePath: string): Promise<string> {
        return this.extractModule(jarPath, modulePath);
    }

    /**
     * Clears the cache for a specific JAR or all JARs.
     */
    clearCache(jarPath?: string): void {
        if (jarPath) {
            this.cache.delete(jarPath);
        } else {
            this.cache.clear();
        }
    }
}