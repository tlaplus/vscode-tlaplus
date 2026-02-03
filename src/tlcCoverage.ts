import * as vscode from 'vscode';
import { CoverageItem } from './model/check';

export interface CoverageLevel {
    name: string;
    minInvocations: number;
    maxInvocations: number;
    opacity: number;
}

interface CoverageThresholds {
    rare: number;
    low: number;
    medium: number;
    high: number;
}

const DEFAULT_THRESHOLDS: CoverageThresholds = {
    rare: 10,
    low: 100,
    medium: 1000,
    high: 10000
};

const COVERAGE_LEVEL_STYLES: Array<Pick<CoverageLevel, 'name' | 'opacity'>> = [
    { name: 'never', opacity: 0.0 },
    { name: 'rare', opacity: 0.2 },
    { name: 'low', opacity: 0.4 },
    { name: 'medium', opacity: 0.6 },
    { name: 'high', opacity: 0.8 },
    { name: 'hot', opacity: 1.0 }
];

export class TlcCoverageDecorationProvider {
    private coverageLevels: CoverageLevel[] = [];
    private enabled = false;
    private decorationTypes = new Map<string, vscode.TextEditorDecorationType>();
    private currentCoverage = new Map<string, CoverageItem[]>(); // filePath -> coverage items
    private totalDistinctStates = 0;
    private disposables: vscode.Disposable[] = [];
    private readonly enabledEmitter = new vscode.EventEmitter<boolean>();
    public readonly onDidChangeEnabled = this.enabledEmitter.event;

    constructor(private context: vscode.ExtensionContext) {
        this.coverageLevels = this.buildCoverageLevels(DEFAULT_THRESHOLDS);
        this.createDecorationTypes();
        this.applyConfiguration();
        this.registerEventHandlers();
    }

    private createDecorationTypes() {
        const baseColor = '#ff0000';
        const wholeLine = false;

        COVERAGE_LEVEL_STYLES.forEach(level => {
            const color = this.hexToRgba(baseColor, level.opacity);
            const decType = vscode.window.createTextEditorDecorationType({
                backgroundColor: color,
                overviewRulerColor: color,
                overviewRulerLane: vscode.OverviewRulerLane.Left,
                isWholeLine: wholeLine,
                rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed
            });
            this.decorationTypes.set(level.name, decType);
        });
    }

    private hexToRgba(hex: string, opacity: number): string {
        const r = parseInt(hex.slice(1, 3), 16);
        const g = parseInt(hex.slice(3, 5), 16);
        const b = parseInt(hex.slice(5, 7), 16);
        return `rgba(${r}, ${g}, ${b}, ${opacity * 0.3})`; // Max 30% opacity for readability
    }


    private registerEventHandlers() {
        // Update decorations when active editor changes
        this.disposables.push(
            vscode.window.onDidChangeActiveTextEditor(editor => {
                if (editor && this.enabled) {
                    this.updateDecorations(editor);
                }
            })
        );

        // Listen for configuration changes
        this.disposables.push(
            vscode.workspace.onDidChangeConfiguration(event => {
                if (event.affectsConfiguration('tlaplus.tlc.profiler.relativeScale') ||
                    event.affectsConfiguration('tlaplus.tlc.profiler.thresholds') ||
                    event.affectsConfiguration('tlaplus.tlc.profiler.enabled')) {
                    this.handleConfigurationChange(event);
                }
            })
        );
    }

    public updateCoverage(coverageItems: CoverageItem[], totalDistinctStates?: number) {
        // Clear existing coverage
        this.currentCoverage.clear();

        // Update total distinct states if provided
        if (totalDistinctStates !== undefined) {
            this.totalDistinctStates = totalDistinctStates;
        }

        // Group coverage items by file
        for (const item of coverageItems) {
            if (!item.filePath) {continue;}

            if (!this.currentCoverage.has(item.filePath)) {
                this.currentCoverage.set(item.filePath, []);
            }
            const items = this.currentCoverage.get(item.filePath);
            if (items) {
                items.push(item);
            }
        }

        // Update all visible editors
        if (this.enabled) {
            this.updateAllEditors();
        }
    }

    private updateAllEditors() {
        vscode.window.visibleTextEditors.forEach(editor => {
            this.updateDecorations(editor);
        });
    }

    private updateDecorations(editor: vscode.TextEditor) {
        const filePath = editor.document.uri.fsPath;
        const coverageItems = this.currentCoverage.get(filePath) || [];

        // Clear all decorations first
        this.decorationTypes.forEach(decType => {
            editor.setDecorations(decType, []);
        });

        if (!this.enabled || coverageItems.length === 0) {
            return;
        }

        // Group decorations by level
        const decorationsByLevel = new Map<string, vscode.DecorationOptions[]>();
        this.coverageLevels.forEach(level => {
            decorationsByLevel.set(level.name, []);
        });

        // Calculate max invocations for relative scaling
        const maxInvocations = Math.max(...coverageItems.map(item => item.total), 1);
        const useRelativeScale = vscode.workspace.getConfiguration('tlaplus.tlc.profiler')
            .get<boolean>('relativeScale', false);

        // Process each coverage item
        for (const item of coverageItems) {
            const level = this.getInvocationLevel(item.total, maxInvocations, useRelativeScale);
            const decoration: vscode.DecorationOptions = {
                range: item.range,
                hoverMessage: this.createHoverMessage(item)
            };
            const decorations = decorationsByLevel.get(level.name);
            if (decorations) {
                decorations.push(decoration);
            }
        }

        // Apply decorations
        decorationsByLevel.forEach((decorations, levelName) => {
            const decType = this.decorationTypes.get(levelName);
            if (decType && decorations.length > 0) {
                editor.setDecorations(decType, decorations);
            }
        });
    }

    private getInvocationLevel(
        invocations: number,
        maxInvocations: number,
        useRelativeScale: boolean
    ): CoverageLevel {
        if (useRelativeScale) {
            // Scale based on percentage of max invocations
            const percentage = (invocations / maxInvocations) * 100;
            if (percentage === 0) {return this.getCoverageLevelByIndex(0);}
            if (percentage <= 1) {return this.getCoverageLevelByIndex(1);}
            if (percentage <= 10) {return this.getCoverageLevelByIndex(2);}
            if (percentage <= 30) {return this.getCoverageLevelByIndex(3);}
            if (percentage <= 60) {return this.getCoverageLevelByIndex(4);}
            return this.getCoverageLevelByIndex(5);
        } else {
            // Use absolute thresholds
            for (const level of this.coverageLevels) {
                if (invocations >= level.minInvocations && invocations <= level.maxInvocations) {
                    return level;
                }
            }
            return this.getCoverageLevelByIndex(5); // hot
        }
    }

    private createHoverMessage(item: CoverageItem): vscode.MarkdownString {
        const md = new vscode.MarkdownString();
        md.appendMarkdown(`**Action ${item.action}:**\n`);
        const percentage = item.total > 0 ? ((item.distinct / item.total) * 100).toFixed(2) : '0.00';
        md.appendMarkdown(`- ${item.total} states found with ${item.distinct} distinct (${percentage}%)\n`);

        // Add contribution percentage if we have total distinct states
        if (this.totalDistinctStates > 0) {
            const contributionPct = ((item.distinct / this.totalDistinctStates) * 100).toFixed(2);
            md.appendMarkdown(`- Contributes ${contributionPct}% to total number of `);
            md.appendMarkdown('distinct states across all actions\n');
        }

        return md;
    }

    public setEnabled(enabled: boolean) {
        if (this.enabled === enabled) {
            return;
        }
        this.enabled = enabled;
        this.enabledEmitter.fire(enabled);
        if (enabled) {
            this.updateAllEditors();
        } else {
            this.clearAllDecorations();
        }
    }

    public isEnabled(): boolean {
        return this.enabled;
    }

    public clearCoverage() {
        this.currentCoverage.clear();
        this.clearAllDecorations();
    }

    private clearAllDecorations() {
        vscode.window.visibleTextEditors.forEach(editor => {
            this.decorationTypes.forEach(decType => {
                editor.setDecorations(decType, []);
            });
        });
    }

    private disposeDecorationTypes() {
        this.decorationTypes.forEach(decType => decType.dispose());
        this.decorationTypes.clear();
    }

    public dispose() {
        this.disposeDecorationTypes();
        this.disposables.forEach(d => d.dispose());
        this.enabledEmitter.dispose();
    }

    private applyConfiguration() {
        const config = vscode.workspace.getConfiguration('tlaplus.tlc.profiler');
        const thresholds = this.normalizeThresholds(config.get<unknown>('thresholds'));
        this.coverageLevels = this.buildCoverageLevels(thresholds);
        const enabled = config.get<boolean>('enabled', false);
        this.setEnabled(enabled);
    }

    private handleConfigurationChange(event: vscode.ConfigurationChangeEvent) {
        const config = vscode.workspace.getConfiguration('tlaplus.tlc.profiler');
        let shouldUpdate = false;

        if (event.affectsConfiguration('tlaplus.tlc.profiler.thresholds')) {
            const thresholds = this.normalizeThresholds(config.get<unknown>('thresholds'));
            this.coverageLevels = this.buildCoverageLevels(thresholds);
            shouldUpdate = true;
        }

        if (event.affectsConfiguration('tlaplus.tlc.profiler.enabled')) {
            const enabled = config.get<boolean>('enabled', false);
            this.setEnabled(enabled);
        }

        if (event.affectsConfiguration('tlaplus.tlc.profiler.relativeScale')) {
            shouldUpdate = true;
        }

        if (shouldUpdate) {
            this.updateAllEditors();
        }
    }

    private normalizeThresholds(raw: unknown): CoverageThresholds {
        if (!raw || typeof raw !== 'object') {
            return DEFAULT_THRESHOLDS;
        }

        const rawRecord = raw as Record<string, unknown>;
        const toInt = (value: unknown): number | undefined => {
            if (typeof value === 'number' && Number.isFinite(value)) {
                return Math.trunc(value);
            }
            if (typeof value === 'string' && value.trim().length > 0) {
                const parsed = Number(value);
                if (Number.isFinite(parsed)) {
                    return Math.trunc(parsed);
                }
            }
            return undefined;
        };

        const rare = toInt(rawRecord.rare);
        const low = toInt(rawRecord.low);
        const medium = toInt(rawRecord.medium);
        const high = toInt(rawRecord.high);

        if (rare === undefined || low === undefined || medium === undefined || high === undefined) {
            return DEFAULT_THRESHOLDS;
        }

        if (rare < 1 || !(rare < low && low < medium && medium < high)) {
            return DEFAULT_THRESHOLDS;
        }

        return { rare, low, medium, high };
    }

    private buildCoverageLevels(thresholds: CoverageThresholds): CoverageLevel[] {
        return [
            {
                ...COVERAGE_LEVEL_STYLES[0],
                minInvocations: 0,
                maxInvocations: 0
            },
            {
                ...COVERAGE_LEVEL_STYLES[1],
                minInvocations: 1,
                maxInvocations: thresholds.rare
            },
            {
                ...COVERAGE_LEVEL_STYLES[2],
                minInvocations: thresholds.rare + 1,
                maxInvocations: thresholds.low
            },
            {
                ...COVERAGE_LEVEL_STYLES[3],
                minInvocations: thresholds.low + 1,
                maxInvocations: thresholds.medium
            },
            {
                ...COVERAGE_LEVEL_STYLES[4],
                minInvocations: thresholds.medium + 1,
                maxInvocations: thresholds.high
            },
            {
                ...COVERAGE_LEVEL_STYLES[5],
                minInvocations: thresholds.high + 1,
                maxInvocations: Infinity
            }
        ];
    }

    private getCoverageLevelByIndex(index: number): CoverageLevel {
        if (index < 0) {
            return this.coverageLevels[0];
        }
        if (index >= this.coverageLevels.length) {
            return this.coverageLevels[this.coverageLevels.length - 1];
        }
        return this.coverageLevels[index];
    }
}
