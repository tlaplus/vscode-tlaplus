import * as vscode from 'vscode';
import { SanyData, SanyStdoutParser } from '../parsers/sany';
import { runSany, runXMLExporter } from '../tla2tools';
import { sanyCache } from './sanyCache';
import { dependencyTracker } from './dependencyTracker';
import { DelayedFn } from '../common';
import { XMLParser } from 'fast-xml-parser';
import { TlaSymbolInformation } from '../symbols/tlaSymbols';
import { performanceMonitor } from './performanceMonitor';

/**
 * XML entry structure from TLA+ XML exporter
 */
interface XmlEntry {
    UID?: {
        $name: string;
    };
    level?: {
        _: string;
    };
    location?: {
        $beginLine?: string;
        $beginColumn?: string;
        $endLine?: string;
        $endColumn?: string;
    };
    kind?: {
        _: string;
    };
}

const CFG_SANY_DEBOUNCE_DELAY = 'tlaplus.sany.debounceDelay';
const DEFAULT_DEBOUNCE_DELAY = 500;

/**
 * Result from SANY execution (either from cache or fresh execution)
 */
export interface SanyExecutionResult {
    sanyData: SanyData;
    symbols: vscode.SymbolInformation[];
    fromCache: boolean;
    executionTime: number;
}

/**
 * Represents a pending SANY execution request
 */
interface PendingExecution {
    filePath: string;
    resolve: (result: SanyExecutionResult) => void;
    reject: (error: Error) => void;
    timestamp: number;
    includeSymbols: boolean;
}

/**
 * Statistics for debounced SANY manager
 */
export interface DebouncedStats {
    totalPending: number;
    activeExecutions: number;
    averageWaitTime: number;
}

/**
 * Manages debounced execution of SANY to prevent redundant parsing operations
 * and provides intelligent caching with dependency tracking.
 */
export class DebouncedSanyManager {
    private readonly pendingExecutions = new Map<string, PendingExecution[]>();
    private readonly debouncedExecutions = new Map<string, DelayedFn>();
    private readonly activeExecutions = new Set<string>();

    constructor() {
        // Clean up on configuration changes
        vscode.workspace.onDidChangeConfiguration((event) => {
            if (event.affectsConfiguration(CFG_SANY_DEBOUNCE_DELAY)) {
                this.updateDebounceDelays();
            }
        });
    }

    /**
     * Get the current debounce delay from configuration
     */
    private getDebounceDelay(): number {
        return vscode.workspace.getConfiguration().get<number>(
            CFG_SANY_DEBOUNCE_DELAY,
            DEFAULT_DEBOUNCE_DELAY
        );
    }

    /**
     * Update debounce delays for all pending executions
     */
    private updateDebounceDelays(): void {
        const newDelay = this.getDebounceDelay();
        // Clear existing debounced functions and recreate with new delay
        for (const [filePath] of this.debouncedExecutions) {
            this.debouncedExecutions.set(filePath, new DelayedFn(newDelay));
        }
    }

    /**
     * Execute SANY parsing with caching and debouncing
     */
    public async executeSany(
        filePath: string,
        includeSymbols: boolean = false
    ): Promise<SanyExecutionResult> {
        // Check cache first
        const cachedResult = await this.getCachedResult(filePath, includeSymbols);
        if (cachedResult) {
            return cachedResult;
        }

        // Return promise that will be resolved when execution completes
        return new Promise<SanyExecutionResult>((resolve, reject) => {
            const execution: PendingExecution = {
                filePath,
                resolve,
                reject,
                timestamp: Date.now(),
                includeSymbols
            };

            // Add to pending executions
            const pending = this.pendingExecutions.get(filePath) || [];
            pending.push(execution);
            this.pendingExecutions.set(filePath, pending);

            // Setup or restart debounced execution
            this.scheduleExecution(filePath);
        });
    }

    /**
     * Check cache for existing result
     */
    private async getCachedResult(
        filePath: string,
        includeSymbols: boolean
    ): Promise<SanyExecutionResult | undefined> {
        const cacheEntry = await sanyCache.get(filePath);
        if (!cacheEntry) {
            performanceMonitor.recordEvent({ type: 'cache_miss', filePath });
            return undefined;
        }

        // If we need symbols but cache doesn't have them, don't use cache
        if (includeSymbols && (!cacheEntry.symbols || cacheEntry.symbols.length === 0)) {
            performanceMonitor.recordEvent({ type: 'cache_miss', filePath });
            return undefined;
        }

        performanceMonitor.recordEvent({ type: 'cache_hit', filePath, fromCache: true });

        return {
            sanyData: cacheEntry.sanyData,
            symbols: cacheEntry.symbols || [],
            fromCache: true,
            executionTime: 0
        };
    }

    /**
     * Schedule debounced execution for a file
     */
    private scheduleExecution(filePath: string): void {
        let delayedFn = this.debouncedExecutions.get(filePath);
        if (!delayedFn) {
            delayedFn = new DelayedFn(this.getDebounceDelay());
            this.debouncedExecutions.set(filePath, delayedFn);
        }

        delayedFn.do(() => {
            this.performExecution(filePath);
        });
    }

    /**
     * Perform the actual SANY execution
     */
    private async performExecution(filePath: string): Promise<void> {
        // Prevent concurrent executions for the same file
        if (this.activeExecutions.has(filePath)) {
            return;
        }

        const pending = this.pendingExecutions.get(filePath);
        if (!pending || pending.length === 0) {
            return;
        }

        this.activeExecutions.add(filePath);
        this.pendingExecutions.delete(filePath);

        const startTime = Date.now();
        let result: SanyExecutionResult;

        performanceMonitor.recordEvent({ type: 'execution_start', filePath });

        try {
            // Check if any pending execution needs symbols
            const needsSymbols = pending.some(p => p.includeSymbols);

            // Scan dependencies first
            const dependencies = await dependencyTracker.scanDependencies(filePath);

            // Execute SANY
            const sanyData = await this.runSanyParsing(filePath);

            // Execute XML exporter for symbols if needed
            let symbols: vscode.SymbolInformation[] = [];
            if (needsSymbols) {
                symbols = await this.runSymbolExtraction(filePath);
            }

            const executionTime = Date.now() - startTime;

            // Cache the results
            await sanyCache.set(filePath, sanyData, symbols, dependencies);

            result = {
                sanyData,
                symbols,
                fromCache: false,
                executionTime
            };

            performanceMonitor.recordEvent({
                type: 'execution_end',
                filePath,
                executionTime,
                fromCache: false
            });

            // Resolve all pending executions
            for (const execution of pending) {
                try {
                    execution.resolve(result);
                } catch (error) {
                    console.warn('Error resolving SANY execution:', error);
                }
            }
        } catch (error) {
            const executionError = error instanceof Error ? error : new Error(String(error));

            performanceMonitor.recordEvent({
                type: 'execution_error',
                filePath,
                error: executionError.message
            });

            // Reject all pending executions
            for (const execution of pending) {
                try {
                    execution.reject(executionError);
                } catch (rejectionError) {
                    console.warn('Error rejecting SANY execution:', rejectionError);
                }
            }
        } finally {
            this.activeExecutions.delete(filePath);
            this.debouncedExecutions.delete(filePath);
        }
    }

    /**
     * Run SANY parsing for the file
     */
    private async runSanyParsing(filePath: string): Promise<SanyData> {
        const processInfo = await runSany(filePath);
        const parser = new SanyStdoutParser(processInfo.process.stdout);
        return parser.readAll();
    }

    /**
     * Run XML symbol extraction
     */
    private async runSymbolExtraction(filePath: string): Promise<vscode.SymbolInformation[]> {
        try {
            const processInfo = await runXMLExporter(filePath, false);

            // Collect stdout
            let stdoutData = '';
            processInfo.process.stdout?.on('data', (data) => {
                stdoutData += data.toString();
            });

            // Wait for process completion
            const exitCode = await new Promise<number>((resolve) => {
                processInfo.process.on('close', (code) => {
                    resolve(code ?? 1);
                });
            });

            if (exitCode !== 0 || !stdoutData) {
                return [];
            }

            // Parse XML and extract symbols
            return this.parseXmlSymbols(stdoutData, vscode.Uri.file(filePath));
        } catch (error) {
            console.warn('Error running XML symbol extraction:', error);
            return [];
        }
    }

    /**
     * Parse XML symbols (simplified version - in production, this would use
     * the existing XML parsing logic from tlaSymbols.ts)
     */
    private parseXmlSymbols(xmlContent: string, documentUri: vscode.Uri): vscode.SymbolInformation[] {
        const symbols: vscode.SymbolInformation[] = [];

        try {
            const parser = new XMLParser({
                ignoreAttributes: false,
                attributeNamePrefix: '$',
                textNodeName: '_'
            });

            const xmlDoc = parser.parse(xmlContent);
            const modules = xmlDoc?.modules?.context;

            if (!modules) {
                return symbols;
            }

            // Parse module symbols (simplified - would be more comprehensive in production)
            const moduleArray = Array.isArray(modules) ? modules : [modules];

            for (const module of moduleArray) {
                if (module.entry) {
                    const entries = Array.isArray(module.entry) ? module.entry : [module.entry];

                    for (const entry of entries) {
                        const symbolInfo = this.createSymbolFromXmlEntry(entry, documentUri);
                        if (symbolInfo) {
                            symbols.push(symbolInfo);
                        }
                    }
                }
            }
        } catch (error) {
            console.warn('Error parsing XML symbols:', error);
        }

        return symbols;
    }

    /**
     * Create a symbol from an XML entry (simplified)
     */
    private createSymbolFromXmlEntry(
        entry: XmlEntry,
        documentUri: vscode.Uri
    ): vscode.SymbolInformation | undefined {
        try {
            const name = entry.UID?.$name || 'unknown';
            const level = parseInt(entry.level?._ || '0');
            const location = entry.location;

            if (!location) {
                return undefined;
            }

            const startLine = parseInt(location.$beginLine || '1') - 1;
            const startChar = parseInt(location.$beginColumn || '1') - 1;
            const endLine = parseInt(location.$endLine || location.$beginLine || '1') - 1;
            const endChar = parseInt(location.$endColumn || location.$beginColumn || '1') - 1;

            const range = new vscode.Range(
                new vscode.Position(startLine, startChar),
                new vscode.Position(endLine, endChar)
            );

            const symbolKind = this.getSymbolKind(entry);

            return new TlaSymbolInformation(
                name,
                symbolKind,
                '',
                new vscode.Location(documentUri, range),
                level
            );
        } catch (error) {
            return undefined;
        }
    }

    /**
     * Determine symbol kind from XML entry
     */
    private getSymbolKind(entry: XmlEntry): vscode.SymbolKind {
        const kind = entry.kind?._;

        switch (kind) {
            case 'ModuleDefinition':
                return vscode.SymbolKind.Module;
            case 'VariableDeclaration':
                return vscode.SymbolKind.Variable;
            case 'ConstantDeclaration':
                return vscode.SymbolKind.Constant;
            case 'OperatorDefinition':
                return vscode.SymbolKind.Function;
            case 'FunctionDefinition':
                return vscode.SymbolKind.Function;
            case 'Theorem':
            case 'Lemma':
            case 'Proposition':
                return vscode.SymbolKind.Property;
            default:
                return vscode.SymbolKind.Field;
        }
    }

    /**
     * Get statistics about pending and active executions
     */
    public getStats(): DebouncedStats {
        let totalPending = 0;
        let totalWaitTime = 0;
        const now = Date.now();

        for (const pending of this.pendingExecutions.values()) {
            totalPending += pending.length;
            for (const execution of pending) {
                totalWaitTime += now - execution.timestamp;
            }
        }

        const averageWaitTime = totalPending > 0 ? totalWaitTime / totalPending : 0;

        return {
            totalPending,
            activeExecutions: this.activeExecutions.size,
            averageWaitTime
        };
    }

    /**
     * Cancel all pending executions for a file
     */
    public cancelPending(filePath: string): void {
        const pending = this.pendingExecutions.get(filePath);
        if (pending) {
            for (const execution of pending) {
                execution.reject(new Error('Execution cancelled'));
            }
            this.pendingExecutions.delete(filePath);
        }

        const delayedFn = this.debouncedExecutions.get(filePath);
        if (delayedFn) {
            delayedFn.cancel();
            this.debouncedExecutions.delete(filePath);
        }
    }

    /**
     * Clear all pending executions
     */
    public clearAll(): void {
        for (const [filePath] of this.pendingExecutions) {
            this.cancelPending(filePath);
        }
    }

    /**
     * Alias for clearAll() to maintain compatibility with existing tests
     */
    public clear(): void {
        this.clearAll();
    }

    /**
     * Get count of pending executions for a file
     */
    public getPendingCount(filePath?: string): number {
        if (filePath) {
            const pending = this.pendingExecutions.get(filePath);
            return pending ? pending.length : 0;
        }
        let total = 0;
        for (const pending of this.pendingExecutions.values()) {
            total += pending.length;
        }
        return total;
    }

    /**
     * Check if a file is currently executing
     */
    public isExecuting(filePath: string): boolean {
        return this.activeExecutions.has(filePath);
    }
}

// Global debounced SANY manager instance
export const debouncedSanyManager = new DebouncedSanyManager();