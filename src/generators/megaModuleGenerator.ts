import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { promisify } from 'util';
import { JarModuleReader, ModuleInfo } from '../utils/jarReader';
import { ModuleRegistry } from '../symbols/moduleRegistry';
import { ModuleParser } from '../parsers/moduleParser';

const writeFile = promisify(fs.writeFile);
const mkdir = promisify(fs.mkdir);
const exists = promisify(fs.exists);
const stat = promisify(fs.stat);

export interface MegaModuleGenerator {
    generateStandardModules(): Promise<string>;
    generateCommunityModules(): Promise<string>;
    generateTLAPSModules(): Promise<string>;
    getCachePath(): string;
    isStale(): Promise<boolean>;
}


/**
 * Generates mega-modules that EXTEND all available TLA+ modules.
 */
export class TlaMegaModuleGenerator implements MegaModuleGenerator {
    private readonly jarReader: JarModuleReader;
    private readonly cacheDir: string;
    private readonly STANDARD_MODULE_NAME = '_ALL_STANDARD';
    private readonly COMMUNITY_MODULE_NAME = '_ALL_CM';
    private readonly TLAPS_MODULE_NAME = '_ALL_TLAPS';
    private readonly moduleParser: ModuleParser;
    private readonly standardRegistry: ModuleRegistry;
    private readonly communityRegistry: ModuleRegistry;

    constructor(
        private readonly toolsJarPath: string,
        private readonly communityJarPath: string,
        private readonly workspaceFolder?: vscode.WorkspaceFolder
    ) {
        this.jarReader = new JarModuleReader();
        this.cacheDir = this.determineCacheDir();
        this.moduleParser = new ModuleParser();
        this.standardRegistry = new ModuleRegistry();
        this.communityRegistry = new ModuleRegistry();
    }

    /**
     * Gets the cache directory path.
     */
    getCachePath(): string {
        return this.cacheDir;
    }

    /**
     * Determines the cache directory based on workspace and fallback to temp.
     */
    private determineCacheDir(): string {
        if (this.workspaceFolder) {
            return path.join(this.workspaceFolder.uri.fsPath, '.vscode', 'tla-index');
        }
        // Fallback to OS temp directory
        const tmpDir = process.env.TEMP || process.env.TMP || '/tmp';
        return path.join(tmpDir, 'vscode-tlaplus-index');
    }

    /**
     * Ensures the cache directory exists.
     */
    private async ensureCacheDir(): Promise<void> {
        try {
            await mkdir(this.cacheDir, { recursive: true });

            // Add .gitignore if in workspace
            if (this.workspaceFolder) {
                const gitignorePath = path.join(this.cacheDir, '.gitignore');
                if (!await exists(gitignorePath)) {
                    await writeFile(gitignorePath, '*\n');
                }
            }
        } catch (error) {
            throw new Error(`Failed to create cache directory: ${error}`);
        }
    }

    /**
     * Ensures the temp directory exists.
     */
    private async ensureTempDir(): Promise<void> {
        const tempDir = path.join(this.cacheDir, 'temp');
        await mkdir(tempDir, { recursive: true });
    }

    /**
     * Generates the standard modules mega-module.
     */
    async generateStandardModules(): Promise<string> {
        const modules = await this.jarReader.listModules(this.toolsJarPath);
        const standardModules = modules.filter(m => m.category === 'standard');

        // Clear and rebuild the registry
        this.standardRegistry.clear();

        // Parse each module individually to build the registry
        console.log(`Building module registry for ${standardModules.length} standard modules...`);
        for (const moduleInfo of standardModules) {
            try {
                // Extract module content from JAR
                const moduleContent = await this.jarReader.extractModuleContent(
                    this.toolsJarPath,
                    moduleInfo.internalPath
                );

                // Parse the module and add to registry
                await this.moduleParser.parseModule(moduleContent, moduleInfo.name, this.standardRegistry);
            } catch (error) {
                console.error(`Failed to parse module ${moduleInfo.name}:`, error);
            }
        }

        // Save the registry
        const registryPath = path.join(this.cacheDir, 'standard-modules.registry.json');
        await this.standardRegistry.save(registryPath);
        console.log(`Module registry saved to ${registryPath}`);

        // Generate the mega-module
        const content = this.generateMegaModule(
            this.STANDARD_MODULE_NAME,
            standardModules,
            'TLA+ Standard Modules',
            ''
        );

        const filePath = path.join(this.cacheDir, `${this.STANDARD_MODULE_NAME}.tla`);
        await this.ensureCacheDir();
        await writeFile(filePath, content, 'utf8');

        return filePath;
    }

    /**
     * Generates the community modules mega-module.
     */
    async generateCommunityModules(): Promise<string> {
        const modules = await this.jarReader.listModules(this.communityJarPath);
        const communityModules = modules.filter(m => m.category === 'community');

        // Clear and rebuild the registry
        this.communityRegistry.clear();

        // Parse each module individually to build the registry
        console.log(`Building module registry for ${communityModules.length} community modules...`);
        for (const moduleInfo of communityModules) {
            try {
                // Extract module content from JAR
                const moduleContent = await this.jarReader.extractModuleContent(
                    this.communityJarPath,
                    moduleInfo.internalPath
                );

                // Parse the module and add to registry
                await this.moduleParser.parseModule(moduleContent, moduleInfo.name, this.communityRegistry);
            } catch (error) {
                console.error(`Failed to parse module ${moduleInfo.name}:`, error);
            }
        }

        // Save the registry
        const registryPath = path.join(this.cacheDir, 'community-modules.registry.json');
        await this.communityRegistry.save(registryPath);
        console.log(`Module registry saved to ${registryPath}`);

        // Generate the mega-module
        const content = this.generateMegaModule(
            this.COMMUNITY_MODULE_NAME,
            communityModules,
            'CommunityModules',
            'Repository: https://github.com/tlaplus/CommunityModules'
        );

        const filePath = path.join(this.cacheDir, `${this.COMMUNITY_MODULE_NAME}.tla`);
        await this.ensureCacheDir();
        await writeFile(filePath, content, 'utf8');

        return filePath;
    }

    /**
     * Generates the TLAPS modules mega-module.
     * Note: This is a placeholder for future TLAPS integration.
     */
    async generateTLAPSModules(): Promise<string> {
        // TODO: Implement when TLAPS JAR is available
        const filePath = path.join(this.cacheDir, `${this.TLAPS_MODULE_NAME}.tla`);
        const content = `---- MODULE ${this.TLAPS_MODULE_NAME} ----
(* TLAPS modules will be available in a future release *)
====`;

        await this.ensureCacheDir();
        await writeFile(filePath, content, 'utf8');

        return filePath;
    }

    /**
     * Checks if the cached modules are stale.
     */
    async isStale(): Promise<boolean> {
        try {
            // Check if cache directory exists
            if (!await exists(this.cacheDir)) {
                return true;
            }

            // Check if mega-module files exist
            const standardPath = path.join(this.cacheDir, `${this.STANDARD_MODULE_NAME}.tla`);
            const communityPath = path.join(this.cacheDir, `${this.COMMUNITY_MODULE_NAME}.tla`);

            if (!await exists(standardPath) || !await exists(communityPath)) {
                return true;
            }

            // Check JAR modification times
            const toolsJarStat = await stat(this.toolsJarPath);
            const communityJarStat = await stat(this.communityJarPath);
            const standardStat = await stat(standardPath);
            const communityStat = await stat(communityPath);

            // If JARs are newer than cached files, regenerate
            if (toolsJarStat.mtime > standardStat.mtime ||
                communityJarStat.mtime > communityStat.mtime) {
                return true;
            }

            return false;
        } catch {
            // Any error means we should regenerate
            return true;
        }
    }

    /**
     * Generates a mega-module content.
     */
    private generateMegaModule(
        moduleName: string,
        modules: ModuleInfo[],
        description: string,
        additionalInfo: string
    ): string {
        const timestamp = new Date().toISOString();
        const sortedModules = modules.sort((a, b) => a.name.localeCompare(b.name));

        // Split modules into chunks of 10 for better formatting
        const moduleChunks: string[][] = [];
        for (let i = 0; i < sortedModules.length; i += 10) {
            moduleChunks.push(sortedModules.slice(i, i + 10).map(m => m.name));
        }

        let content = `---- MODULE ${moduleName} ----
(* Auto-generated index of ${description}
 * Generated: ${timestamp}
 * Total modules: ${modules.length}`;

        if (additionalInfo) {
            content += `\n * ${additionalInfo}`;
        }

        content += '\n *)\n \n';

        if (moduleChunks.length > 0) {
            content += 'EXTENDS ';
            moduleChunks.forEach((chunk, index) => {
                if (index > 0) {
                    content += ',\n        ';
                }
                content += chunk.join(', ');
            });
        }

        // Add excluded modules comment if any
        const excludedModules = this.getExcludedModules(moduleName);
        if (excludedModules.length > 0) {
            content += `\n        \n(* Internal modules excluded: ${excludedModules.join(', ')} *)`;
        }

        content += '\n====';

        return content;
    }

    /**
     * Gets the list of excluded modules for a given mega-module.
     */
    private getExcludedModules(moduleName: string): string[] {
        if (moduleName === this.STANDARD_MODULE_NAME) {
            return [
                'MC', 'MCAliases', 'MCRealTime', '_JsonTrace',
                '_TLAPlusCounterExample', '_TLAPlusDebugger', 'SubsetValue'
            ];
        }
        return [];
    }

    /**
     * Regenerates all mega-modules if needed.
     */
    async regenerateIfNeeded(): Promise<boolean> {
        if (await this.isStale()) {
            await this.generateStandardModules();
            await this.generateCommunityModules();
            return true;
        }
        return false;
    }

    /**
     * Forces regeneration of all mega-modules.
     */
    async forceRegenerate(): Promise<void> {
        await this.generateStandardModules();
        await this.generateCommunityModules();
    }

    /**
     * Clears the cache directory.
     */
    async clearCache(): Promise<void> {
        if (await exists(this.cacheDir)) {
            const files = await promisify(fs.readdir)(this.cacheDir);
            for (const file of files) {
                if (file.endsWith('.tla')) {
                    await promisify(fs.unlink)(path.join(this.cacheDir, file));
                }
            }
        }
    }
}