import * as vscode from 'vscode';
import { JarModuleReader } from '../utils/jarReader';
import * as path from 'path';

/**
 * Provides virtual documents for viewing TLA+ module sources from JAR files.
 */
export class ModuleDocumentProvider implements vscode.TextDocumentContentProvider {
    private readonly cache = new Map<string, string>();

    constructor(
        private readonly jarReader: JarModuleReader,
        private readonly toolsJarPath: string,
        private readonly communityJarPath: string
    ) {}

    /**
     * Provides the content for a virtual TLA+ module document.
     */
    async provideTextDocumentContent(uri: vscode.Uri): Promise<string> {
        // URI format: tla-module://category/ModuleName.tla
        // The category is in the authority, and the path starts with /
        const category = uri.authority;
        const fileName = uri.path.startsWith('/') ? uri.path.substring(1) : uri.path;
        const moduleName = path.basename(fileName, '.tla');

        if (!category || !moduleName) {
            throw new Error(`Invalid module URI format: ${uri.toString()}`);
        }

        // Check cache first
        const cacheKey = `${category}/${moduleName}`;
        const cached = this.cache.get(cacheKey);
        if (cached) {
            return cached;
        }

        // Determine JAR path based on category
        const jarPath = category === 'standard' ? this.toolsJarPath : this.communityJarPath;

        // Find the module in the JAR
        const modules = await this.jarReader.listModules(jarPath);
        const module = modules.find(m => m.name === moduleName && m.category === category);

        if (!module) {
            // Debug information
            const availableModules = modules.filter(m => m.category === category).map(m => m.name);
            console.error(`Module ${moduleName} not found in ${category} modules. ` +
                `Available: ${availableModules.join(', ')}`);
            throw new Error(`Module ${moduleName} not found in ${category} modules`);
        }

        // Extract module content
        const content = await this.jarReader.extractModule(module.jarPath, module.internalPath);

        // Add header comment
        const header = `(* This is a read-only view of ${moduleName} from ${category} modules\n` +
                      ` * Source: ${path.basename(jarPath)}\n` +
                      ` * Path: ${module.internalPath}\n` +
                      ' *)\n\n';

        const fullContent = header + content;

        // Cache the content
        this.cache.set(cacheKey, fullContent);

        return fullContent;
    }

    /**
     * Clears the document cache.
     */
    clearCache(): void {
        this.cache.clear();
    }
}