import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { promisify } from 'util';
import { JarModuleReader } from '../utils/jarReader';
import { ModuleRegistry } from '../symbols/moduleRegistry';
import { ModuleParser } from '../parsers/moduleParser';

const writeFile = promisify(fs.writeFile);
const mkdir = promisify(fs.mkdir);
const exists = promisify(fs.exists);
const stat = promisify(fs.stat);

export interface ModuleRegistryGenerator {
    generateStandardModules(): Promise<void>;
    generateCommunityModules(): Promise<void>;
    getCachePath(): string;
    isStale(): Promise<boolean>;
    clearCache(): Promise<void>;
}


/**
 * Generates module registries for TLA+ standard and community modules.
 */
export class TlaMegaModuleGenerator implements ModuleRegistryGenerator {
    private readonly jarReader: JarModuleReader;
    private readonly cacheDir: string;
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
     * Generates the standard modules registry.
     */
    async generateStandardModules(): Promise<void> {
        await this.ensureCacheDir();

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
        console.log(`Standard module registry saved to ${registryPath}`);
    }

    /**
     * Generates the community modules registry.
     */
    async generateCommunityModules(): Promise<void> {
        await this.ensureCacheDir();

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
        console.log(`Community module registry saved to ${registryPath}`);
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

            // Check if registry files exist
            const standardPath = path.join(this.cacheDir, 'standard-modules.registry.json');
            const communityPath = path.join(this.cacheDir, 'community-modules.registry.json');

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
     * Clears the cache directory.
     */
    async clearCache(): Promise<void> {
        const fs = await import('fs');
        const { promisify } = await import('util');
        const rm = promisify(fs.rm);

        try {
            if (await exists(this.cacheDir)) {
                await rm(this.cacheDir, { recursive: true, force: true });
            }
        } catch (error) {
            console.error('Failed to clear cache:', error);
            throw error;
        }
    }

}
