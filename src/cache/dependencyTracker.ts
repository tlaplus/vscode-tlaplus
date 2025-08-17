import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { sanyCache } from './sanyCache';

/**
 * Information about a file's dependencies
 */
interface DependencyInfo {
    filePath: string;
    dependencies: string[];
    lastScanned: number;
}

/**
 * Statistics for dependency tracking
 */
export interface DependencyStats {
    totalFiles: number;
    totalDependencies: number;
    averageDependencies: number;
}

/**
 * Tracks TLA+ module dependencies (EXTENDS and INSTANCE relationships)
 * and automatically invalidates cache when dependencies change.
 */
export class DependencyTracker {
    private readonly dependencies = new Map<string, DependencyInfo>();
    private readonly fileWatchers = new Map<string, vscode.FileSystemWatcher>();
    private isScanning = false;

    constructor() {
        // Listen for file system changes
        this.setupGlobalFileWatcher();
    }

    /**
     * Setup global file watcher for TLA+ files
     */
    private setupGlobalFileWatcher(): void {
        const watcher = vscode.workspace.createFileSystemWatcher('**/*.tla');

        watcher.onDidChange((uri) => {
            this.handleFileChange(uri.fsPath);
        });

        watcher.onDidDelete((uri) => {
            this.handleFileDelete(uri.fsPath);
        });

        watcher.onDidCreate((uri) => {
            this.handleFileCreate(uri.fsPath);
        });
    }

    /**
     * Handle file change events
     */
    private async handleFileChange(filePath: string): Promise<void> {
        if (this.isScanning) {
            return;
        }

        // Invalidate cache for the changed file
        sanyCache.invalidate(filePath);

        // Invalidate cache for files that depend on this file
        sanyCache.invalidateDependents(filePath);

        // Re-scan dependencies for the changed file
        await this.scanDependencies(filePath);

        // Invalidate dependents again in case dependencies changed
        sanyCache.invalidateDependents(filePath);
    }

    /**
     * Handle file deletion events
     */
    private handleFileDelete(filePath: string): void {
        // Remove from dependency tracking
        this.dependencies.delete(filePath);

        // Stop watching this file specifically
        const watcher = this.fileWatchers.get(filePath);
        if (watcher) {
            watcher.dispose();
            this.fileWatchers.delete(filePath);
        }

        // Invalidate cache
        sanyCache.invalidate(filePath);
        sanyCache.invalidateDependents(filePath);
    }

    /**
     * Handle file creation events
     */
    private async handleFileCreate(filePath: string): Promise<void> {
        // Scan dependencies for the new file
        await this.scanDependencies(filePath);
    }

    /**
     * Extract module dependencies from TLA+ file content
     */
    private extractDependencies(content: string, filePath: string): string[] {
        const dependencies: string[] = [];
        const lines = content.split('\n');
        const fileDir = path.dirname(filePath);

        for (const line of lines) {
            const trimmedLine = line.trim();

            // Skip comments
            if (this.isComment(trimmedLine)) {
                continue;
            }

            // Process different statement types
            this.extractExtendsModules(trimmedLine, fileDir, dependencies);
            this.extractInstanceModules(trimmedLine, fileDir, dependencies);
        }

        return [...new Set(dependencies)]; // Remove duplicates
    }

    /**
     * Check if a line is a comment
     */
    private isComment(line: string): boolean {
        return line.startsWith('\\*') || line.startsWith('(*');
    }

    /**
     * Extract modules from EXTENDS statements
     */
    private extractExtendsModules(line: string, baseDir: string, dependencies: string[]): void {
        const extendsRegex = /^EXTENDS\s+(.+)$/;
        const match = extendsRegex.exec(line);
        
        if (!match) {
            return;
        }

        const modules = match[1].split(',').map(m => m.trim());
        this.addModuleDependencies(modules, baseDir, dependencies);
    }

    /**
     * Extract modules from INSTANCE statements
     */
    private extractInstanceModules(line: string, baseDir: string, dependencies: string[]): void {
        // Try assignment-style INSTANCE first
        const assignmentRegex = /^(\w+)\s*==\s*INSTANCE\s+(\w+)/;
        let match = assignmentRegex.exec(line);
        
        if (match) {
            this.addModuleDependencies([match[2]], baseDir, dependencies);
            return;
        }

        // Try inline INSTANCE
        const inlineRegex = /INSTANCE\s+(\w+)/;
        match = inlineRegex.exec(line);
        
        if (match) {
            this.addModuleDependencies([match[1]], baseDir, dependencies);
        }
    }

    /**
     * Add module dependencies to the list
     */
    private addModuleDependencies(modules: string[], baseDir: string, dependencies: string[]): void {
        for (const module of modules) {
            const modulePath = this.resolveModulePath(module, baseDir);
            if (modulePath) {
                dependencies.push(modulePath);
            }
        }
    }

    /**
     * Resolve module name to file path
     */
    private resolveModulePath(moduleName: string, baseDir: string): string | undefined {
        // Check if it's a standard library module
        const standardModules = [
            'TLC', 'Naturals', 'Integers', 'Reals', 'Sequences', 'FiniteSets',
            'Bags', 'RealTime', 'TLCExt', 'IOUtils', 'Json', 'CSV', 'Toolbox',
            'SVG', 'Randomization', 'Relation', 'Functions', 'Apalache',
            'BagsExt', 'FiniteSetsExt', 'FunctionsExt', 'SequencesExt',
            'VectorClocks', 'Bitwise', 'DifferentialEquations', 'Graphs'
        ];

        if (standardModules.includes(moduleName)) {
            return undefined; // Don't track standard library dependencies
        }

        // Try to find the module file in order of priority
        const possiblePaths = [
            // Same directory as the current file
            path.join(baseDir, `${moduleName}.tla`),
            // Parent directory
            path.join(baseDir, '..', `${moduleName}.tla`),
            // Common spec or modules directories
            path.join(baseDir, '..', 'modules', `${moduleName}.tla`),
            path.join(baseDir, '..', 'specs', `${moduleName}.tla`),
        ];

        for (const possiblePath of possiblePaths) {
            try {
                if (fs.existsSync(possiblePath)) {
                    return path.resolve(possiblePath);
                }
            } catch (error) {
                // Log the error but continue trying other paths
                console.debug(`Failed to check path ${possiblePath}: ${error}`);
            }
        }

        // Try workspace search for the module
        return this.findModuleInWorkspace(moduleName);
    }

    /**
     * Find module in workspace folders
     */
    private findModuleInWorkspace(moduleName: string): string | undefined {
        const workspaceFolders = vscode.workspace.workspaceFolders;
        if (!workspaceFolders) {
            return undefined;
        }

        // Search in each workspace folder
        for (const folder of workspaceFolders) {
            const possiblePath = path.join(folder.uri.fsPath, `${moduleName}.tla`);
            try {
                if (fs.existsSync(possiblePath)) {
                    return path.resolve(possiblePath);
                }
            } catch (error) {
                // Log the error but continue searching other workspace folders
                console.debug(`Failed to check workspace path ${possiblePath}: ${error}`);
            }
        }

        // For now, return undefined since we can't do async search here
        // In the future, this could be improved with a cached workspace file index
        return undefined;
    }

    /**
     * Scan dependencies for a specific file
     */
    public async scanDependencies(filePath: string): Promise<string[]> {
        try {
            this.isScanning = true;
            const content = await fs.promises.readFile(filePath, 'utf8');
            const dependencies = this.extractDependencies(content, filePath);

            // Store dependency information
            this.dependencies.set(filePath, {
                filePath,
                dependencies,
                lastScanned: Date.now()
            });

            return dependencies;
        } catch (error) {
            // Handle file read errors
            console.debug(`Failed to scan dependencies for ${filePath}: ${error}`);
            this.dependencies.delete(filePath);
            return [];
        } finally {
            this.isScanning = false;
        }
    }

    /**
     * Get dependencies for a file (from cache if available)
     */
    public getDependencies(filePath: string): string[] {
        const info = this.dependencies.get(filePath);
        return info ? info.dependencies : [];
    }

    /**
     * Get all files that depend on the given file
     */
    public getDependents(filePath: string): string[] {
        const dependents: string[] = [];
        const normalizedPath = path.resolve(filePath);

        for (const [file, info] of this.dependencies) {
            const normalizedDeps = info.dependencies.map(dep => path.resolve(dep));
            if (normalizedDeps.includes(normalizedPath)) {
                dependents.push(file);
            }
        }

        return dependents;
    }

    /**
     * Clear all dependency information
     */
    public clear(): void {
        this.dependencies.clear();
        for (const watcher of this.fileWatchers.values()) {
            watcher.dispose();
        }
        this.fileWatchers.clear();
    }

    /**
     * Get statistics about tracked dependencies
     */
    public getStats(): DependencyStats {
        const totalFiles = this.dependencies.size;
        let totalDependencies = 0;

        for (const info of this.dependencies.values()) {
            totalDependencies += info.dependencies.length;
        }

        const averageDependencies = totalFiles > 0 ? totalDependencies / totalFiles : 0;

        return {
            totalFiles,
            totalDependencies,
            averageDependencies
        };
    }

    /**
     * Check if a file has been scanned for dependencies
     */
    public hasBeenScanned(filePath: string): boolean {
        return this.dependencies.has(filePath);
    }

    /**
     * Get the last scan time for a file
     */
    public getLastScanTime(filePath: string): number | undefined {
        const info = this.dependencies.get(filePath);
        return info?.lastScanned;
    }

    /**
     * Force rescan of all tracked files
     */
    public async rescanAll(): Promise<void> {
        const files = Array.from(this.dependencies.keys());
        for (const file of files) {
            await this.scanDependencies(file);
        }
    }

    /**
     * Get dependency graph for visualization
     */
    public getDependencyGraph(): Map<string, string[]> {
        const graph = new Map<string, string[]>();

        for (const [file, info] of this.dependencies) {
            graph.set(file, [...info.dependencies]);
        }

        return graph;
    }

    /**
     * Check if a file has been recently scanned (within specified time)
     */
    public isRecentlyScanned(filePath: string, maxAgeMs: number = 60000): boolean {
        const info = this.dependencies.get(filePath);
        if (!info) {
            return false;
        }

        const age = Date.now() - info.lastScanned;
        return age <= maxAgeMs;
    }

    /**
     * Get all dependencies as a Map
     */
    public getAllDependencies(): Map<string, string[]> {
        const result = new Map<string, string[]>();

        for (const [file, info] of this.dependencies) {
            result.set(file, [...info.dependencies]);
        }

        return result;
    }

    /**
     * Get all tracked files
     */
    public getTrackedFiles(): string[] {
        return Array.from(this.dependencies.keys());
    }
}

// Global dependency tracker instance
export const dependencyTracker = new DependencyTracker();