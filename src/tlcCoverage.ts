import * as vscode from 'vscode';
import { CoverageItem } from './model/check';

export interface CoverageLevel {
    name: string;
    minInvocations: number;
    maxInvocations: number;
    opacity: number;
}

export class TlcCoverageDecorationProvider {
    private static readonly COVERAGE_LEVELS: CoverageLevel[] = [
        { name: 'never', minInvocations: 0, maxInvocations: 0, opacity: 0.0 },
        { name: 'rare', minInvocations: 1, maxInvocations: 10, opacity: 0.2 },
        { name: 'low', minInvocations: 11, maxInvocations: 100, opacity: 0.4 },
        { name: 'medium', minInvocations: 101, maxInvocations: 1000, opacity: 0.6 },
        { name: 'high', minInvocations: 1001, maxInvocations: 10000, opacity: 0.8 },
        { name: 'hot', minInvocations: 10001, maxInvocations: Infinity, opacity: 1.0 }
    ];

    private enabled = false;
    private decorationTypes = new Map<string, vscode.TextEditorDecorationType>();
    private currentCoverage = new Map<string, CoverageItem[]>(); // filePath -> coverage items
    private totalDistinctStates = 0;
    private disposables: vscode.Disposable[] = [];

    constructor(private context: vscode.ExtensionContext) {
        this.createDecorationTypes();
        this.registerEventHandlers();
    }

    private createDecorationTypes() {
        const baseColor = '#ff0000';
        const wholeLine = false;

        TlcCoverageDecorationProvider.COVERAGE_LEVELS.forEach(level => {
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
                    event.affectsConfiguration('tlaplus.tlc.profiler.thresholds')) {
                    this.updateAllEditors();
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
        TlcCoverageDecorationProvider.COVERAGE_LEVELS.forEach(level => {
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
            if (percentage === 0) {return TlcCoverageDecorationProvider.COVERAGE_LEVELS[0];}
            if (percentage <= 1) {return TlcCoverageDecorationProvider.COVERAGE_LEVELS[1];}
            if (percentage <= 10) {return TlcCoverageDecorationProvider.COVERAGE_LEVELS[2];}
            if (percentage <= 30) {return TlcCoverageDecorationProvider.COVERAGE_LEVELS[3];}
            if (percentage <= 60) {return TlcCoverageDecorationProvider.COVERAGE_LEVELS[4];}
            return TlcCoverageDecorationProvider.COVERAGE_LEVELS[5];
        } else {
            // Use absolute thresholds
            for (const level of TlcCoverageDecorationProvider.COVERAGE_LEVELS) {
                if (invocations >= level.minInvocations && invocations <= level.maxInvocations) {
                    return level;
                }
            }
            return TlcCoverageDecorationProvider.COVERAGE_LEVELS[5]; // hot
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
        this.enabled = enabled;
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
    }
}