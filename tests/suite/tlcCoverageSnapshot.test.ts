import * as assert from 'assert';
import * as vscode from 'vscode';
import { CoverageItem } from '../../src/model/check';
import { buildTlcCoverageSnapshot, TlcCoverageSettings } from '../../src/tlcCoverageSnapshot';

const ABSOLUTE_SETTINGS: TlcCoverageSettings = {
    enabled: false,
    relativeScale: false,
    thresholds: {
        rare: 10,
        low: 100,
        medium: 1000,
        high: 10000
    }
};

suite('TLC Coverage Snapshot Test Suite', () => {
    test('classifies TLC coverage buckets with absolute thresholds', () => {
        const snapshot = buildTlcCoverageSnapshot([
            coverageItem('Never', 0, 0),
            coverageItem('Rare', 5, 3),
            coverageItem('Covered', 75, 25),
            coverageItem('Hot', 12000, 50)
        ], 100, ABSOLUTE_SETTINGS);

        assert.deepStrictEqual(
            snapshot.entries.map((entry) => [entry.item.action, entry.level, entry.bucket]),
            [
                ['Never', 'never', 'uncovered'],
                ['Rare', 'rare', 'rare'],
                ['Covered', 'low', 'covered'],
                ['Hot', 'hot', 'hot']
            ]
        );
        assert.strictEqual(snapshot.entries[2].totalShareOfDistinctStates, 25);
        assert.strictEqual(snapshot.entries[3].totalShareOfDistinctStates, 50);
    });

    test('classifies TLC coverage buckets with relative scaling', () => {
        const snapshot = buildTlcCoverageSnapshot([
            coverageItem('Never', 0, 0),
            coverageItem('Rare', 1, 1),
            coverageItem('Covered', 30, 10),
            coverageItem('Hot', 100, 20)
        ], 20, {
            ...ABSOLUTE_SETTINGS,
            relativeScale: true
        });

        assert.deepStrictEqual(
            snapshot.entries.map((entry) => [entry.item.action, entry.level, entry.bucket]),
            [
                ['Never', 'never', 'uncovered'],
                ['Rare', 'rare', 'rare'],
                ['Covered', 'medium', 'covered'],
                ['Hot', 'hot', 'hot']
            ]
        );
    });
});

function coverageItem(action: string, total: number, distinct: number): CoverageItem {
    return new CoverageItem('Spec', action, '/tmp/spec.tla', new vscode.Range(0, 0, 0, 4), total, distinct);
}
