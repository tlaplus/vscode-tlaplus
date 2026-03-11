import * as vscode from 'vscode';
import {
    getTlcCoverageSettings,
    TLC_COVERAGE_LEVELS,
    TlcCoverageLevelName,
    TlcCoverageSnapshotEntry,
    TlcCoverageSnapshotStore
} from './tlcCoverageSnapshot';

export class TlcCoverageDecorationProvider implements vscode.Disposable {
    private enabled = getTlcCoverageSettings().enabled;
    private readonly decorationTypes = new Map<TlcCoverageLevelName, vscode.TextEditorDecorationType>();
    private readonly disposables: vscode.Disposable[] = [];

    constructor(private readonly coverageSnapshotStore: TlcCoverageSnapshotStore) {
        this.createDecorationTypes();
        this.disposables.push(
            this.coverageSnapshotStore.onDidChangeSnapshot(() => {
                if (this.enabled) {
                    this.updateAllEditors();
                }
            }),
            vscode.window.onDidChangeActiveTextEditor((editor) => {
                if (editor && this.enabled) {
                    this.updateDecorations(editor);
                }
            }),
            vscode.workspace.onDidChangeConfiguration((event) => {
                if (event.affectsConfiguration('tlaplus.tlc.profiler.enabled')) {
                    this.setEnabled(getTlcCoverageSettings().enabled);
                }
            })
        );
    }

    setEnabled(enabled: boolean): void {
        this.enabled = enabled;
        if (enabled) {
            this.updateAllEditors();
        } else {
            this.clearAllDecorations();
        }
    }

    isEnabled(): boolean {
        return this.enabled;
    }

    clearCoverage(): void {
        this.coverageSnapshotStore.clearCoverage();
        this.clearAllDecorations();
    }

    dispose(): void {
        this.clearAllDecorations();
        for (const decorationType of this.decorationTypes.values()) {
            decorationType.dispose();
        }
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
    }

    private createDecorationTypes(): void {
        for (const level of TLC_COVERAGE_LEVELS) {
            const redColor = this.getColorWithOpacity('#ff0000', level.opacity * 0.3);
            const decorationType = vscode.window.createTextEditorDecorationType({
                backgroundColor: redColor,
                borderRadius: '2px',
                overviewRulerColor: redColor,
                overviewRulerLane: vscode.OverviewRulerLane.Left,
                isWholeLine: false,
                rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed
            });
            this.decorationTypes.set(level.name, decorationType);
        }
    }

    private updateAllEditors(): void {
        for (const editor of vscode.window.visibleTextEditors) {
            this.updateDecorations(editor);
        }
    }

    private updateDecorations(editor: vscode.TextEditor): void {
        this.clearDecorations(editor);
        if (!this.enabled) {
            return;
        }

        const entries = this.coverageSnapshotStore.getSnapshot().entriesByFile.get(editor.document.uri.fsPath) ?? [];
        if (entries.length === 0) {
            return;
        }

        const decorationsByLevel = new Map<TlcCoverageLevelName, vscode.DecorationOptions[]>();
        for (const entry of entries) {
            const decorations = decorationsByLevel.get(entry.level) ?? [];
            decorations.push({
                range: entry.item.range,
                hoverMessage: this.createHoverMessage(entry)
            });
            decorationsByLevel.set(entry.level, decorations);
        }

        for (const level of TLC_COVERAGE_LEVELS) {
            const decorationType = this.decorationTypes.get(level.name);
            if (decorationType) {
                editor.setDecorations(decorationType, decorationsByLevel.get(level.name) ?? []);
            }
        }
    }

    private clearAllDecorations(): void {
        for (const editor of vscode.window.visibleTextEditors) {
            this.clearDecorations(editor);
        }
    }

    private clearDecorations(editor: vscode.TextEditor): void {
        for (const decorationType of this.decorationTypes.values()) {
            editor.setDecorations(decorationType, []);
        }
    }

    private createHoverMessage(entry: TlcCoverageSnapshotEntry): vscode.MarkdownString {
        const markdown = new vscode.MarkdownString();
        markdown.appendMarkdown(`**Action ${entry.item.action}:**\n`);
        markdown.appendMarkdown(
            `- ${entry.item.total} states found with ${entry.item.distinct} distinct (${entry.distinctRatio.toFixed(2)}%)\n`
        );
        if (entry.totalShareOfDistinctStates > 0) {
            markdown.appendMarkdown(
                `- Contributes ${entry.totalShareOfDistinctStates.toFixed(2)}% to the total distinct states across all actions\n`
            );
        }
        return markdown;
    }

    private getColorWithOpacity(hexColor: string, opacity: number): string {
        const hex = hexColor.replace('#', '');
        const r = parseInt(hex.slice(0, 2), 16);
        const g = parseInt(hex.slice(2, 4), 16);
        const b = parseInt(hex.slice(4, 6), 16);
        return `rgba(${r}, ${g}, ${b}, ${opacity})`;
    }
}
