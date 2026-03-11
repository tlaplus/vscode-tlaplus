import * as vscode from 'vscode';
import { CoverageItem } from './model/check';

export type TlcCoverageLevelName = 'never' | 'rare' | 'low' | 'medium' | 'high' | 'hot';
export type TlcCoverageBucket = 'uncovered' | 'rare' | 'covered' | 'hot';

export interface TlcCoverageThresholds {
    rare: number;
    low: number;
    medium: number;
    high: number;
}

export interface TlcCoverageSettings {
    enabled: boolean;
    relativeScale: boolean;
    thresholds: TlcCoverageThresholds;
}

export interface TlcCoverageLevel {
    name: TlcCoverageLevelName;
    opacity: number;
}

export interface TlcCoverageSnapshotEntry {
    item: CoverageItem;
    level: TlcCoverageLevelName;
    bucket: TlcCoverageBucket;
    distinctRatio: number;
    totalShareOfDistinctStates: number;
}

export interface TlcCoverageSnapshot {
    items: readonly CoverageItem[];
    entries: readonly TlcCoverageSnapshotEntry[];
    entriesByBucket: ReadonlyMap<TlcCoverageBucket, readonly TlcCoverageSnapshotEntry[]>;
    entriesByFile: ReadonlyMap<string, readonly TlcCoverageSnapshotEntry[]>;
    maxInvocations: number;
    totalDistinctStates: number;
    settings: TlcCoverageSettings;
}

export const TLC_COVERAGE_LEVELS: readonly TlcCoverageLevel[] = [
    { name: 'never', opacity: 0.0 },
    { name: 'rare', opacity: 0.2 },
    { name: 'low', opacity: 0.4 },
    { name: 'medium', opacity: 0.6 },
    { name: 'high', opacity: 0.8 },
    { name: 'hot', opacity: 1.0 }
];

const DEFAULT_THRESHOLDS: TlcCoverageThresholds = {
    rare: 10,
    low: 100,
    medium: 1000,
    high: 10000
};

export function getTlcCoverageSettings(
    configuration = vscode.workspace.getConfiguration('tlaplus.tlc.profiler')
): TlcCoverageSettings {
    return {
        enabled: configuration.get<boolean>('enabled', false),
        relativeScale: configuration.get<boolean>('relativeScale', false),
        thresholds: normalizeThresholds(configuration.get<unknown>('thresholds'))
    };
}

export function classifyTlcCoverageLevel(
    invocations: number,
    maxInvocations: number,
    settings: TlcCoverageSettings
): TlcCoverageLevelName {
    if (settings.relativeScale) {
        const percentage = maxInvocations <= 0 ? 0 : invocations / maxInvocations * 100;
        if (percentage === 0) {return 'never';}
        if (percentage <= 1) {return 'rare';}
        if (percentage <= 10) {return 'low';}
        if (percentage <= 30) {return 'medium';}
        if (percentage <= 60) {return 'high';}
        return 'hot';
    }

    if (invocations === 0) {return 'never';}
    if (invocations <= settings.thresholds.rare) {return 'rare';}
    if (invocations <= settings.thresholds.low) {return 'low';}
    if (invocations <= settings.thresholds.medium) {return 'medium';}
    if (invocations <= settings.thresholds.high) {return 'high';}
    return 'hot';
}

export function toTlcCoverageBucket(level: TlcCoverageLevelName): TlcCoverageBucket {
    if (level === 'never') {return 'uncovered';}
    if (level === 'rare') {return 'rare';}
    if (level === 'hot') {return 'hot';}
    return 'covered';
}

export function buildTlcCoverageSnapshot(
    items: readonly CoverageItem[],
    totalDistinctStates = 0,
    settings = getTlcCoverageSettings()
): TlcCoverageSnapshot {
    const safeItems = [...items];
    const maxInvocations = Math.max(1, ...safeItems.map(item => item.total));
    const entries = safeItems.map((item) => {
        const level = classifyTlcCoverageLevel(item.total, maxInvocations, settings);
        return {
            item,
            level,
            bucket: toTlcCoverageBucket(level),
            distinctRatio: item.total === 0 ? 0 : item.distinct / item.total * 100,
            totalShareOfDistinctStates: totalDistinctStates === 0 ? 0 : item.distinct / totalDistinctStates * 100
        } satisfies TlcCoverageSnapshotEntry;
    });

    const entriesByBucket = new Map<TlcCoverageBucket, TlcCoverageSnapshotEntry[]>([
        ['uncovered', []],
        ['rare', []],
        ['covered', []],
        ['hot', []]
    ]);
    const entriesByFile = new Map<string, TlcCoverageSnapshotEntry[]>();

    for (const entry of entries) {
        entriesByBucket.get(entry.bucket)?.push(entry);
        if (!entry.item.filePath) {
            continue;
        }
        const fileEntries = entriesByFile.get(entry.item.filePath) ?? [];
        fileEntries.push(entry);
        entriesByFile.set(entry.item.filePath, fileEntries);
    }

    return {
        items: safeItems,
        entries,
        entriesByBucket,
        entriesByFile,
        maxInvocations,
        totalDistinctStates,
        settings
    };
}

export class TlcCoverageSnapshotStore implements vscode.Disposable {
    private readonly changeEmitter = new vscode.EventEmitter<TlcCoverageSnapshot>();
    private readonly disposables: vscode.Disposable[] = [this.changeEmitter];
    private coverageItems: CoverageItem[] = [];
    private totalDistinctStates = 0;
    private snapshot = buildTlcCoverageSnapshot([]);

    readonly onDidChangeSnapshot = this.changeEmitter.event;

    constructor() {
        this.disposables.push(
            vscode.workspace.onDidChangeConfiguration((event) => {
                if (
                    event.affectsConfiguration('tlaplus.tlc.profiler.relativeScale') ||
                    event.affectsConfiguration('tlaplus.tlc.profiler.thresholds')
                ) {
                    this.rebuildSnapshot();
                }
            })
        );
    }

    getSnapshot(): TlcCoverageSnapshot {
        return this.snapshot;
    }

    updateCoverage(items: readonly CoverageItem[], totalDistinctStates = 0): void {
        this.coverageItems = [...items];
        this.totalDistinctStates = totalDistinctStates;
        this.rebuildSnapshot();
    }

    clearCoverage(): void {
        this.coverageItems = [];
        this.totalDistinctStates = 0;
        this.rebuildSnapshot();
    }

    dispose(): void {
        for (const disposable of this.disposables) {
            disposable.dispose();
        }
    }

    private rebuildSnapshot(): void {
        this.snapshot = buildTlcCoverageSnapshot(this.coverageItems, this.totalDistinctStates);
        this.changeEmitter.fire(this.snapshot);
    }
}

function normalizeThresholds(raw: unknown): TlcCoverageThresholds {
    const candidate = typeof raw === 'object' && raw !== null
        ? raw as Partial<Record<keyof TlcCoverageThresholds, unknown>>
        : {};
    const rare = readThreshold(candidate.rare, DEFAULT_THRESHOLDS.rare);
    const low = Math.max(rare, readThreshold(candidate.low, DEFAULT_THRESHOLDS.low));
    const medium = Math.max(low, readThreshold(candidate.medium, DEFAULT_THRESHOLDS.medium));
    const high = Math.max(medium, readThreshold(candidate.high, DEFAULT_THRESHOLDS.high));
    return { rare, low, medium, high };
}

function readThreshold(value: unknown, fallback: number): number {
    const numberValue = typeof value === 'number' ? value : Number(value);
    return Number.isFinite(numberValue) && numberValue >= 0 ? numberValue : fallback;
}
