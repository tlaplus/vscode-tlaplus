import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { SanyData } from '../parsers/sany';

const CFG_SANY_CACHE_ENABLED = 'tlaplus.sany.cache.enabled';
const CFG_SANY_CACHE_MAX_SIZE = 'tlaplus.sany.cache.maxSize';
const DEFAULT_MAX_SIZE_MB = 50;

/**
 * Represents a cached SANY parse result entry
 */
export interface CacheEntry {
    fileHash: string;
    lastModified: number;
    sanyData: SanyData;
    symbols: vscode.SymbolInformation[];
    dependencies: string[];
    timestamp: number;
}

/**
 * Statistics for cache performance tracking
 */
export interface CacheStatistics {
    hits: number;
    misses: number;
    evictions: number;
    totalSize: number;
    entries: number;
}

/**
 * LRU cache for SANY parse results to avoid redundant parsing operations.
 * Caches both diagnostic information and symbol data with intelligent invalidation
 * based on file content changes and dependency relationships.
 */
export class SanyCache {
    private readonly cache = new Map<string, CacheEntry>();
    private readonly accessOrder = new Map<string, number>();
    private accessCounter = 0;
    private stats: CacheStatistics = {
        hits: 0,
        misses: 0,
        evictions: 0,
        totalSize: 0,
        entries: 0
    };

    constructor() {
        // Listen for configuration changes
        vscode.workspace.onDidChangeConfiguration((event) => {
            if (event.affectsConfiguration(CFG_SANY_CACHE_ENABLED)) {
                if (!this.isEnabled()) {
                    this.clear();
                }
            } else if (event.affectsConfiguration(CFG_SANY_CACHE_MAX_SIZE)) {
                this.enforceMemoryLimit();
            }
        });

        // Listen for file changes to invalidate cache
        vscode.workspace.onDidChangeTextDocument((event) => {
            if (event.document.languageId === 'tlaplus' || event.document.languageId === 'tlaplus_cfg') {
                // Invalidate cache for the changed file
                this.invalidate(event.document.fileName);
                // Also invalidate files that depend on this one
                this.invalidateDependents(event.document.fileName);
            }
        });

        // Also listen for file saves (in case text changes aren't enough)
        vscode.workspace.onDidSaveTextDocument((document) => {
            if (document.languageId === 'tlaplus' || document.languageId === 'tlaplus_cfg') {
                this.invalidate(document.fileName);
                this.invalidateDependents(document.fileName);
            }
        });
    }

    /**
     * Check if caching is enabled via configuration
     */
    private isEnabled(): boolean {
        return vscode.workspace.getConfiguration().get<boolean>(CFG_SANY_CACHE_ENABLED, true);
    }

    /**
     * Get the maximum cache size in bytes
     */
    private getMaxSizeBytes(): number {
        const maxSizeMB = vscode.workspace.getConfiguration().get<number>(
            CFG_SANY_CACHE_MAX_SIZE,
            DEFAULT_MAX_SIZE_MB
        );
        return maxSizeMB * 1024 * 1024;
    }

    /**
     * Generate a cache key for a file based on its path
     */
    private getCacheKey(filePath: string): string {
        return vscode.Uri.file(filePath).toString();
    }

    /**
     * Calculate file hash for content-based caching (simple string hash)
     */
    private async calculateFileHash(filePath: string): Promise<string> {
        try {
            const content = await fs.promises.readFile(filePath, 'utf8');
            // Simple string hash function (djb2 algorithm)
            let hash = 5381;
            for (let i = 0; i < content.length; i++) {
                hash = ((hash << 5) + hash) + content.charCodeAt(i);
            }
            return (hash >>> 0).toString(16); // Convert to unsigned 32-bit hex
        } catch (error) {
            // If file can't be read, return a hash based on the path and current time
            const fallback = filePath + Date.now();
            let hash = 5381;
            for (let i = 0; i < fallback.length; i++) {
                hash = ((hash << 5) + hash) + fallback.charCodeAt(i);
            }
            return (hash >>> 0).toString(16);
        }
    }

    /**
     * Get file modification time
     */
    private async getFileModTime(filePath: string): Promise<number> {
        try {
            const stats = await fs.promises.stat(filePath);
            return stats.mtime.getTime();
        } catch (error) {
            return 0;
        }
    }

    /**
     * Estimate the memory size of a cache entry
     */
    private estimateEntrySize(entry: CacheEntry): number {
        // Rough estimation: base entry size + symbols + diagnostics
        let size = 1000; // Base overhead

        // Estimate symbols size
        size += entry.symbols.length * 500; // Rough estimate per symbol

        // Estimate diagnostics size
        const messages = entry.sanyData.dCollection.getMessages();
        size += messages.length * 200; // Rough estimate per diagnostic message

        // Dependencies
        size += entry.dependencies.join('').length * 2;

        return size;
    }

    /**
     * Update access order for LRU eviction
     */
    private updateAccessOrder(key: string): void {
        this.accessOrder.set(key, ++this.accessCounter);
    }

    /**
     * Find the least recently used entry
     */
    private findLRUKey(): string | undefined {
        let lruKey: string | undefined;
        let minAccess = Infinity;

        for (const [key, accessTime] of this.accessOrder) {
            if (accessTime < minAccess) {
                minAccess = accessTime;
                lruKey = key;
            }
        }

        return lruKey;
    }

    /**
     * Enforce memory limit by evicting LRU entries
     */
    private enforceMemoryLimit(): void {
        const maxSize = this.getMaxSizeBytes();

        while (this.stats.totalSize > maxSize && this.cache.size > 0) {
            const lruKey = this.findLRUKey();
            if (lruKey) {
                this.evict(lruKey);
            } else {
                break;
            }
        }
    }

    /**
     * Evict an entry from the cache
     */
    private evict(key: string): void {
        const entry = this.cache.get(key);
        if (entry) {
            const entrySize = this.estimateEntrySize(entry);
            this.cache.delete(key);
            this.accessOrder.delete(key);
            this.stats.totalSize -= entrySize;
            this.stats.entries--;
            this.stats.evictions++;
        }
    }

    /**
     * Check if cached entry is valid for the given file
     */
    private async isEntryValid(filePath: string, entry: CacheEntry): Promise<boolean> {
        const currentHash = await this.calculateFileHash(filePath);
        const currentModTime = await this.getFileModTime(filePath);

        return entry.fileHash === currentHash && entry.lastModified === currentModTime;
    }

    /**
     * Get cached SANY data for a file
     */
    public async get(filePath: string): Promise<CacheEntry | undefined> {
        if (!this.isEnabled()) {
            return undefined;
        }

        const key = this.getCacheKey(filePath);
        const entry = this.cache.get(key);

        if (!entry) {
            this.stats.misses++;
            return undefined;
        }

        // Check if entry is still valid
        if (!(await this.isEntryValid(filePath, entry))) {
            this.cache.delete(key);
            this.accessOrder.delete(key);
            const entrySize = this.estimateEntrySize(entry);
            this.stats.totalSize -= entrySize;
            this.stats.entries--;
            this.stats.misses++;
            return undefined;
        }

        this.updateAccessOrder(key);
        this.stats.hits++;
        return entry;
    }

    /**
     * Store SANY data in cache
     */
    public async set(
        filePath: string,
        sanyData: SanyData,
        symbols: vscode.SymbolInformation[],
        dependencies: string[] = []
    ): Promise<void> {
        if (!this.isEnabled()) {
            return;
        }

        const key = this.getCacheKey(filePath);
        const fileHash = await this.calculateFileHash(filePath);
        const lastModified = await this.getFileModTime(filePath);

        const entry: CacheEntry = {
            fileHash,
            lastModified,
            sanyData,
            symbols,
            dependencies,
            timestamp: Date.now()
        };

        // Remove existing entry if present
        const existingEntry = this.cache.get(key);
        if (existingEntry) {
            const existingSize = this.estimateEntrySize(existingEntry);
            this.stats.totalSize -= existingSize;
        } else {
            this.stats.entries++;
        }

        this.cache.set(key, entry);
        this.updateAccessOrder(key);

        const entrySize = this.estimateEntrySize(entry);
        this.stats.totalSize += entrySize;

        // Enforce memory limit
        this.enforceMemoryLimit();
    }

    /**
     * Invalidate cache entry for a specific file
     */
    public invalidate(filePath: string): void {
        const key = this.getCacheKey(filePath);
        this.evict(key);
    }

    /**
     * Invalidate cache entries that depend on the given file
     */
    public invalidateDependents(filePath: string): void {
        const keysToInvalidate: string[] = [];

        for (const [key, entry] of this.cache) {
            // Normalize paths for comparison
            const normalizedFilePath = path.resolve(filePath);
            const normalizedDeps = entry.dependencies.map(dep => path.resolve(dep));

            if (normalizedDeps.includes(normalizedFilePath)) {
                keysToInvalidate.push(key);
            }
        }

        for (const key of keysToInvalidate) {
            this.evict(key);
        }
    }

    /**
     * Clear all cache entries
     */
    public clear(): void {
        this.cache.clear();
        this.accessOrder.clear();
        this.stats = {
            hits: 0,
            misses: 0,
            evictions: 0,
            totalSize: 0,
            entries: 0
        };
    }

    /**
     * Get cache statistics
     */
    public getStats(): Readonly<CacheStatistics> {
        return { ...this.stats };
    }

    /**
     * Get cache hit ratio as a percentage
     */
    public getHitRatio(): number {
        const total = this.stats.hits + this.stats.misses;
        return total > 0 ? (this.stats.hits / total) * 100 : 0;
    }

    /**
     * Check if cache contains an entry for the given file
     */
    public has(filePath: string): boolean {
        const key = this.getCacheKey(filePath);
        return this.cache.has(key);
    }

    /**
     * Get all cached file paths
     */
    public getCachedPaths(): string[] {
        return Array.from(this.cache.keys()).map(key =>
            vscode.Uri.parse(key).fsPath
        );
    }
}

// Global cache instance
export const sanyCache = new SanyCache();