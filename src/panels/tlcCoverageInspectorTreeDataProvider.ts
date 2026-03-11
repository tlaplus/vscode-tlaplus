import * as path from 'path';
import * as vscode from 'vscode';
import { TlcCoverageBucket, TlcCoverageSnapshotEntry, TlcCoverageSnapshotStore } from '../tlcCoverageSnapshot';

export const CMD_SHOW_TLC_COVERAGE_INSPECTOR = 'tlaplus.tlc.profiler.showInspector';
export const CMD_REFRESH_TLC_COVERAGE_INSPECTOR = 'tlaplus.tlc.profiler.refreshInspector';
export const CMD_REVEAL_TLC_COVERAGE_ENTRY = 'tlaplus.tlc.profiler.revealCoverageEntry';

const BUCKET_ORDER: readonly TlcCoverageBucket[] = ['uncovered', 'rare', 'covered', 'hot'];

type CoverageTreeItem = CoverageBucketTreeItem | CoverageEntryTreeItem;

interface CoverageRevealOperations {
    openTextDocument: (uri: vscode.Uri) => Thenable<vscode.TextDocument>;
    showTextDocument: (document: vscode.TextDocument) => Thenable<vscode.TextEditor>;
}

export class TlcCoverageInspectorTreeDataProvider implements vscode.TreeDataProvider<CoverageTreeItem>, vscode.Disposable {
    static readonly viewType = 'tlaplus.tlc-coverage-inspector';

    private readonly changeEmitter = new vscode.EventEmitter<CoverageTreeItem | undefined | void>();
    private readonly disposables: vscode.Disposable[] = [this.changeEmitter];

    readonly onDidChangeTreeData = this.changeEmitter.event;

    constructor(private readonly coverageSnapshotStore: TlcCoverageSnapshotStore) {
        this.disposables.push(
            this.coverageSnapshotStore.onDidChangeSnapshot(() => this.refresh())
        );
    }

    dispose(): void {
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
    }

    refresh(): void {
        this.changeEmitter.fire();
    }

    getMessage(): string | undefined {
        if (this.coverageSnapshotStore.getSnapshot().entries.length === 0) {
            return 'Run TLC model checking to inspect TLC source coverage.';
        }
        return undefined;
    }

    getTreeItem(element: CoverageTreeItem): vscode.TreeItem {
        return element;
    }

    getChildren(element?: CoverageTreeItem): vscode.ProviderResult<CoverageTreeItem[]> {
        if (!element) {
            return this.getBucketItems();
        }
        if (element instanceof CoverageBucketTreeItem) {
            return this.getEntryItems(element.bucket);
        }
        return [];
    }

    private getBucketItems(): CoverageBucketTreeItem[] {
        const snapshot = this.coverageSnapshotStore.getSnapshot();
        return BUCKET_ORDER
            .map((bucket) => new CoverageBucketTreeItem(bucket, snapshot.entriesByBucket.get(bucket)?.length ?? 0))
            .filter((bucketItem) => bucketItem.count > 0);
    }

    private getEntryItems(bucket: TlcCoverageBucket): CoverageEntryTreeItem[] {
        const entries = [...(this.coverageSnapshotStore.getSnapshot().entriesByBucket.get(bucket) ?? [])];
        entries.sort((left, right) => compareEntries(left, right, bucket));
        return entries.map((entry) => new CoverageEntryTreeItem(entry));
    }
}

export async function revealCoverageEntry(
    entry: TlcCoverageSnapshotEntry,
    operations: CoverageRevealOperations = {
        openTextDocument: (uri) => vscode.workspace.openTextDocument(uri),
        showTextDocument: (document) => vscode.window.showTextDocument(document, { preview: false })
    }
): Promise<void> {
    if (!entry.item.filePath) {
        void vscode.window.showInformationMessage('Source navigation is unavailable for this TLC coverage entry.');
        return;
    }

    const document = await operations.openTextDocument(vscode.Uri.file(entry.item.filePath));
    const editor = await operations.showTextDocument(document);
    editor.selection = new vscode.Selection(entry.item.range.start, entry.item.range.end);
    editor.revealRange(entry.item.range, vscode.TextEditorRevealType.InCenter);
}

class CoverageBucketTreeItem extends vscode.TreeItem {
    readonly count: number;

    constructor(readonly bucket: TlcCoverageBucket, count: number) {
        super(getBucketLabel(bucket), vscode.TreeItemCollapsibleState.Expanded);
        this.count = count;
        this.description = `${count}`;
        this.tooltip = `${count} ${getBucketLabel(bucket).toLowerCase()} TLC coverage item${count === 1 ? '' : 's'}`;
        this.iconPath = getBucketIcon(bucket);
    }
}

class CoverageEntryTreeItem extends vscode.TreeItem {
    constructor(readonly entry: TlcCoverageSnapshotEntry) {
        super(entry.item.action, vscode.TreeItemCollapsibleState.None);
        this.description = entry.item.filePath
            ? `${entry.item.distinct}d/${entry.item.total}t`
            : `${entry.item.distinct}d/${entry.item.total}t unavailable`;
        this.tooltip = createEntryTooltip(entry);
        this.contextValue = entry.item.filePath ? 'tlcCoverageEntry' : 'tlcCoverageEntryUnavailable';
        this.iconPath = getBucketIcon(entry.bucket);
        if (entry.item.filePath) {
            this.command = {
                command: CMD_REVEAL_TLC_COVERAGE_ENTRY,
                title: 'Reveal TLC coverage location',
                arguments: [entry]
            };
        }
    }
}

function compareEntries(
    left: TlcCoverageSnapshotEntry,
    right: TlcCoverageSnapshotEntry,
    bucket: TlcCoverageBucket
): number {
    if (bucket === 'uncovered') {
        return compareEntryLabels(left, right);
    }
    if (bucket === 'rare') {
        return left.item.total - right.item.total || left.item.distinct - right.item.distinct || compareEntryLabels(left, right);
    }
    return right.item.total - left.item.total || right.item.distinct - left.item.distinct || compareEntryLabels(left, right);
}

function compareEntryLabels(left: TlcCoverageSnapshotEntry, right: TlcCoverageSnapshotEntry): number {
    return [left.item.module, left.item.action, left.item.filePath ?? '']
        .join(':')
        .localeCompare([right.item.module, right.item.action, right.item.filePath ?? ''].join(':'));
}

function createEntryTooltip(entry: TlcCoverageSnapshotEntry): vscode.MarkdownString {
    const tooltip = new vscode.MarkdownString();
    tooltip.appendMarkdown(`**${entry.item.action}**\n\n`);
    tooltip.appendMarkdown(`- Module: ${entry.item.module}\n`);
    if (entry.item.filePath) {
        tooltip.appendMarkdown(`- File: ${path.basename(entry.item.filePath)}\n`);
    }
    tooltip.appendMarkdown(`- Range: ${formatRange(entry.item.range)}\n`);
    tooltip.appendMarkdown(`- Total hits: ${entry.item.total}\n`);
    tooltip.appendMarkdown(`- Distinct hits: ${entry.item.distinct} (${entry.distinctRatio.toFixed(1)}%)\n`);
    if (entry.totalShareOfDistinctStates > 0) {
        tooltip.appendMarkdown(`- Share of total distinct states: ${entry.totalShareOfDistinctStates.toFixed(1)}%\n`);
    }
    if (!entry.item.filePath) {
        tooltip.appendMarkdown('\nSource navigation unavailable for this TLC coverage entry.');
    }
    return tooltip;
}

function formatRange(range: vscode.Range): string {
    return `line ${range.start.line + 1}, col ${range.start.character + 1}`;
}

function getBucketLabel(bucket: TlcCoverageBucket): string {
    switch (bucket) {
    case 'uncovered':
        return 'Uncovered';
    case 'rare':
        return 'Rare';
    case 'covered':
        return 'Covered';
    case 'hot':
        return 'Hot';
    }
}

function getBucketIcon(bucket: TlcCoverageBucket): vscode.ThemeIcon {
    switch (bucket) {
    case 'uncovered':
        return new vscode.ThemeIcon('circle-large-outline');
    case 'rare':
        return new vscode.ThemeIcon('history');
    case 'covered':
        return new vscode.ThemeIcon('graph-line');
    case 'hot':
        return new vscode.ThemeIcon('flame');
    }
}
