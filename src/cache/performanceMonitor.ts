import * as vscode from 'vscode';
import { sanyCache } from './sanyCache';
import { debouncedSanyManager } from './debouncedSany';
import { dependencyTracker } from './dependencyTracker';

/**
 * Types of performance events
 */
export type PerformanceEventType =
    | 'cache_hit'
    | 'cache_miss'
    | 'execution_start'
    | 'execution_end'
    | 'execution_error'
    | 'cache_eviction'
    | 'dependency_scan';

/**
 * Performance event data
 */
export interface PerformanceEvent {
    type: PerformanceEventType;
    filePath?: string;
    executionTime?: number;
    fromCache?: boolean;
    error?: string;
    timestamp?: number;
}

/**
 * Comprehensive performance metrics
 */
export interface PerformanceMetrics {
    // Cache metrics
    cacheHitRatio: number;
    cacheEntries: number;
    cacheSize: number;
    cacheEvictions: number;

    // Execution metrics
    averageExecutionTime: number;
    totalExecutions: number;
    failedExecutions: number;

    // Debouncing metrics
    pendingExecutions: number;
    activeExecutions: number;
    averageWaitTime: number;

    // Dependency tracking metrics
    trackedFiles: number;
    totalDependencies: number;
    averageDependencies: number;

    // Time period
    startTime: number;
    endTime: number;
}

/**
 * Monitors and tracks performance of the SANY caching system
 * to provide insights into cache effectiveness and execution patterns.
 */
export class PerformanceMonitor {
    private events: (PerformanceEvent & { timestamp: number })[] = [];
    private maxEvents = 1000;
    private startTime = Date.now();
    private isEnabled = true;
    private cleanupInterval: NodeJS.Timeout;
    private statusBarItem: vscode.StatusBarItem | undefined;

    constructor() {
        // Clean up old events periodically
        this.cleanupInterval = setInterval(() => {
            this.cleanupOldEvents();
        }, 60000); // Every minute
    }

    /**
     * Record a performance event
     */
    public recordEvent(event: PerformanceEvent): void {
        if (!this.isEnabled) {
            return;
        }

        this.events.push({
            ...event,
            timestamp: Date.now()
        });

        // Keep only the most recent events
        if (this.events.length > this.maxEvents) {
            this.events = this.events.slice(-this.maxEvents);
        }

        // Update status bar if visible
        if (this.statusBarItem) {
            this.updateStatusBar();
        }
    }

    /**
     * Clean up events older than 1 hour
     */
    private cleanupOldEvents(): void {
        const oneHourAgo = Date.now() - (60 * 60 * 1000);
        this.events = this.events.filter(event => event.timestamp > oneHourAgo);
    }

    /**
     * Get comprehensive performance metrics
     */
    public getMetrics(): PerformanceMetrics {
        const now = Date.now();
        const cacheStats = sanyCache.getStats();
        const debouncedStats = debouncedSanyManager.getStats();
        const dependencyStats = dependencyTracker.getStats();

        // Calculate execution metrics from events
        const executionEvents = this.events.filter(e => e.type === 'execution_end');
        const errorEvents = this.events.filter(e => e.type === 'execution_error');
        const totalExecutions = executionEvents.length;
        const failedExecutions = errorEvents.length;

        const averageExecutionTime = totalExecutions > 0
            ? executionEvents.reduce((sum, e) => sum + (e.executionTime || 0), 0) / totalExecutions
            : 0;

        return {
            // Cache metrics
            cacheHitRatio: sanyCache.getHitRatio(),
            cacheEntries: cacheStats.entries,
            cacheSize: cacheStats.totalSize,
            cacheEvictions: cacheStats.evictions,

            // Execution metrics
            averageExecutionTime,
            totalExecutions,
            failedExecutions,

            // Debouncing metrics
            pendingExecutions: debouncedStats.totalPending,
            activeExecutions: debouncedStats.activeExecutions,
            averageWaitTime: debouncedStats.averageWaitTime,

            // Dependency tracking metrics
            trackedFiles: dependencyStats.totalFiles,
            totalDependencies: dependencyStats.totalDependencies,
            averageDependencies: dependencyStats.averageDependencies,

            // Time period
            startTime: this.startTime,
            endTime: now
        };
    }

    /**
     * Get recent events
     */
    public getRecentEvents(maxCount: number = 100): PerformanceEvent[] {
        return this.events.slice(-maxCount);
    }

    /**
     * Get events for a specific file
     */
    public getFileEvents(filePath: string, maxCount: number = 50): PerformanceEvent[] {
        return this.events
            .filter(event => event.filePath === filePath)
            .slice(-maxCount);
    }

    /**
     * Get performance summary for logging
     */
    public getPerformanceSummary(): string {
        const metrics = this.getMetrics();
        const totalTime = metrics.endTime - metrics.startTime;
        const hours = Math.round(totalTime / (1000 * 60 * 60) * 100) / 100;

        return [
            `SANY Cache Performance Summary (${hours}h):`,
            `  Cache: ${metrics.cacheHitRatio.toFixed(1)}% hit ratio, ` +
                `${metrics.cacheEntries} entries, ${Math.round(metrics.cacheSize / 1024)}KB`,
            `  Execution: ${metrics.totalExecutions} total, ${metrics.failedExecutions} failed, ` +
                `${Math.round(metrics.averageExecutionTime)}ms avg`,
            `  Debouncing: ${metrics.pendingExecutions} pending, ` +
                `${Math.round(metrics.averageWaitTime)}ms avg wait`,
            `  Dependencies: ${metrics.trackedFiles} files, ${metrics.totalDependencies} deps, ` +
                `${metrics.averageDependencies.toFixed(1)} avg/file`
        ].join('\n');
    }

    /**
     * Show performance status in VS Code status bar
     */
    public createStatusBarItem(): vscode.StatusBarItem {
        // Return existing status bar item if already created (singleton pattern)
        if (this.statusBarItem) {
            return this.statusBarItem;
        }

        this.statusBarItem = vscode.window.createStatusBarItem(
            vscode.StatusBarAlignment.Right,
            100
        );

        this.statusBarItem.text = '$(database) SANY Cache';
        this.statusBarItem.tooltip = 'Click to view SANY cache performance';
        this.statusBarItem.command = 'tlaplus.cache.showStats';

        this.updateStatusBar();

        return this.statusBarItem;
    }

    /**
     * Update status bar with current metrics
     */
    private updateStatusBar(): void {
        if (!this.statusBarItem) {
            return;
        }

        const metrics = this.getMetrics();
        const hitRatio = metrics.cacheHitRatio;

        // Show different icons based on cache effectiveness
        let icon = '$(database)';
        if (hitRatio >= 80) {
            icon = '$(pass)';
        } else if (hitRatio >= 50) {
            icon = '$(info)';
        } else if (metrics.cacheEntries > 0) {
            icon = '$(warning)';
        }

        this.statusBarItem.text = `${icon} Cache: ${hitRatio.toFixed(0)}%`;

        // Update tooltip with detailed information
        this.statusBarItem.tooltip = new vscode.MarkdownString(
            `**SANY Cache Performance**\n\n` +
            `Hit Ratio: **${hitRatio.toFixed(1)}%**\n` +
            `Entries: ${metrics.cacheEntries}\n` +
            `Size: ${Math.round(metrics.cacheSize / 1024)}KB\n` +
            `Evictions: ${metrics.cacheEvictions}\n\n` +
            `Click for detailed statistics`
        );
    }

    /**
     * Show performance information in output channel
     */
    public showPerformanceOutput(outputChannel: vscode.OutputChannel): void {
        outputChannel.clear();
        outputChannel.appendLine('='.repeat(60));
        outputChannel.appendLine(this.getPerformanceSummary());
        outputChannel.appendLine('='.repeat(60));
        outputChannel.appendLine('');
        outputChannel.appendLine('Recent Events:');
        outputChannel.appendLine('-'.repeat(40));

        const recentEvents = this.getRecentEvents(20);
        for (const event of recentEvents) {
            const time = event.timestamp ? new Date(event.timestamp).toLocaleTimeString() : 'N/A';
            const file = event.filePath ? path.basename(event.filePath) : 'N/A';
            let eventStr = `[${time}] ${event.type} - ${file}`;

            if (event.executionTime) {
                eventStr += ` (${event.executionTime}ms)`;
            }
            if (event.fromCache) {
                eventStr += ' [CACHED]';
            }
            if (event.error) {
                eventStr += ` ERROR: ${event.error}`;
            }

            outputChannel.appendLine(eventStr);
        }

        outputChannel.show();
    }

    /**
     * Export performance metrics as JSON
     */
    public exportMetrics(): string {
        const metrics = this.getMetrics();
        const events = this.getRecentEvents(100);

        return JSON.stringify({
            metrics,
            events,
            exportTime: new Date().toISOString()
        }, null, 2);
    }

    /**
     * Reset all performance tracking
     */
    public reset(): void {
        this.events = [];
        this.startTime = Date.now();

        if (this.statusBarItem) {
            this.updateStatusBar();
        }
    }

    /**
     * Enable or disable performance monitoring
     */
    public setEnabled(enabled: boolean): void {
        this.isEnabled = enabled;
    }

    /**
     * Dispose of resources
     */
    public dispose(): void {
        if (this.cleanupInterval) {
            clearInterval(this.cleanupInterval);
        }

        if (this.statusBarItem) {
            this.statusBarItem.dispose();
            this.statusBarItem = undefined;
        }
    }

    /**
     * Get cache effectiveness score (0-100)
     */
    public getCacheEffectivenessScore(): number {
        const metrics = this.getMetrics();

        // Weighted score based on multiple factors
        const hitRatioScore = metrics.cacheHitRatio; // 0-100
        const evictionPenalty = Math.max(0, 100 - metrics.cacheEvictions * 2);
        const executionScore = metrics.failedExecutions > 0
            ? Math.max(0, 100 - (metrics.failedExecutions / Math.max(1, metrics.totalExecutions)) * 100)
            : 100;

        // Weighted average
        return (hitRatioScore * 0.6 + evictionPenalty * 0.2 + executionScore * 0.2);
    }

    /**
     * Show detailed statistics
     */
    public async showDetailedStats(): Promise<void> {
        const metrics = this.getMetrics();
        const choice = await vscode.window.showInformationMessage(
            `Cache Hit Ratio: ${metrics.cacheHitRatio.toFixed(1)}%`,
            'Show Details',
            'Export JSON',
            'Reset'
        );

        if (choice === 'Show Details') {
            const outputChannel = vscode.window.createOutputChannel('SANY Cache Performance');
            this.showPerformanceOutput(outputChannel);
        } else if (choice === 'Export JSON') {
            const json = this.exportMetrics();
            await vscode.env.clipboard.writeText(json);
            vscode.window.showInformationMessage('Performance metrics copied to clipboard');
        } else if (choice === 'Reset') {
            this.reset();
            vscode.window.showInformationMessage('Performance tracking reset');
        }
    }

    /**
     * Export data as JSON
     */
    public exportData(): { metrics: PerformanceMetrics; events: PerformanceEvent[]; exportTime: string } {
        return {
            metrics: this.getMetrics(),
            events: this.getRecentEvents(100),
            exportTime: new Date().toISOString()
        };
    }

    /**
     * Generate performance report
     */
    public generateReport(): string {
        const metrics = this.getMetrics();
        const totalTime = metrics.endTime - metrics.startTime;
        const hours = Math.round(totalTime / (1000 * 60 * 60) * 100) / 100;

        const report = [
            '# SANY Cache Performance Report',
            '',
            `## Summary (${hours} hours)`,
            '',
            '### Cache Performance',
            `- Hit Ratio: ${metrics.cacheHitRatio.toFixed(1)}%`,
            `- Total Entries: ${metrics.cacheEntries}`,
            `- Cache Size: ${Math.round(metrics.cacheSize / 1024)}KB`,
            `- Evictions: ${metrics.cacheEvictions}`,
            '',
            '### Execution Metrics',
            `- Total Executions: ${metrics.totalExecutions}`,
            `- Failed Executions: ${metrics.failedExecutions}`,
            `- Average Execution Time: ${Math.round(metrics.averageExecutionTime)}ms`,
            '',
            '### Dependency Tracking',
            `- Tracked Files: ${metrics.trackedFiles}`,
            `- Total Dependencies: ${metrics.totalDependencies}`,
            `- Average Dependencies per File: ${metrics.averageDependencies.toFixed(1)}`,
            '',
            '### System Performance',
            `- Pending Executions: ${metrics.pendingExecutions}`,
            `- Active Executions: ${metrics.activeExecutions}`,
            `- Average Wait Time: ${Math.round(metrics.averageWaitTime)}ms`,
            '',
            '### Effectiveness Score',
            `- Overall Score: ${this.getCacheEffectivenessScore().toFixed(1)}/100`
        ].join('\n');

        return report;
    }

    /**
     * Get cache effectiveness analysis
     */
    public getCacheEffectivenessAnalysis(): {
        score: number;
        analysis: string;
        recommendations: string[];
    } {
        const metrics = this.getMetrics();
        const score = this.getCacheEffectivenessScore();

        let analysis = '';
        const recommendations: string[] = [];

        if (score >= 80) {
            analysis = 'Cache is performing excellently.';
        } else if (score >= 60) {
            analysis = 'Cache is performing well with room for improvement.';
        } else if (score >= 40) {
            analysis = 'Cache performance is moderate.';
        } else {
            analysis = 'Cache performance needs improvement.';
        }

        // Generate recommendations
        if (metrics.cacheHitRatio < 50) {
            recommendations.push('Consider increasing cache size limit');
        }
        if (metrics.cacheEvictions > 10) {
            recommendations.push('Frequent evictions detected - increase memory allocation');
        }
        if (metrics.failedExecutions > metrics.totalExecutions * 0.1) {
            recommendations.push('High failure rate - check SANY configuration');
        }
        if (metrics.averageWaitTime > 1000) {
            recommendations.push('Long wait times - consider reducing debounce delay');
        }

        return { score, analysis, recommendations };
    }
}

// Import path module
import * as path from 'path';

// Global performance monitor instance
export const performanceMonitor = new PerformanceMonitor();