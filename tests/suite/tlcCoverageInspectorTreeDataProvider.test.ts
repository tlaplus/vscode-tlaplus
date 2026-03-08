import * as assert from 'assert';
import * as vscode from 'vscode';
import { CoverageItem } from '../../src/model/check';
import {
    revealCoverageEntry,
    TlcCoverageInspectorTreeDataProvider
} from '../../src/panels/tlcCoverageInspectorTreeDataProvider';
import { buildTlcCoverageSnapshot, TlcCoverageSnapshotStore } from '../../src/tlcCoverageSnapshot';

suite('TLC Coverage Inspector Tree Test Suite', () => {
    test('groups TLC coverage entries into ordered buckets', async () => {
        const store = new TlcCoverageSnapshotStore();
        const provider = new TlcCoverageInspectorTreeDataProvider(store);
        try {
            store.updateCoverage([
                coverageItem('Never', 0, 0),
                coverageItem('Rare', 5, 3),
                coverageItem('Covered', 75, 25),
                coverageItem('Hot', 12000, 50)
            ], 100);

            const roots = await provider.getChildren() as vscode.TreeItem[];
            assert.deepStrictEqual(roots.map((item) => item.label), ['Uncovered', 'Rare', 'Covered', 'Hot']);

            const rareItems = await provider.getChildren(roots[1] as unknown as never) as vscode.TreeItem[];
            assert.strictEqual(rareItems.length, 1);
            assert.strictEqual(rareItems[0].label, 'Rare');
        } finally {
            provider.dispose();
            store.dispose();
        }
    });

    test('keeps unresolved TLC coverage entries visible but non-navigable', async () => {
        const store = new TlcCoverageSnapshotStore();
        const provider = new TlcCoverageInspectorTreeDataProvider(store);
        try {
            store.updateCoverage([
                new CoverageItem('Spec', 'Never', undefined, new vscode.Range(0, 0, 0, 4), 0, 0)
            ], 0);

            const roots = await provider.getChildren() as vscode.TreeItem[];
            const entries = await provider.getChildren(roots[0] as unknown as never) as vscode.TreeItem[];
            const tooltip = entries[0].tooltip as vscode.MarkdownString;

            assert.strictEqual(entries[0].command, undefined);
            assert.match(tooltip.value, /navigation unavailable/i);
        } finally {
            provider.dispose();
            store.dispose();
        }
    });

    test('reveals TLC coverage entries at the recorded source range', async () => {
        const entry = buildTlcCoverageSnapshot([
            coverageItem('Next', 5, 2, '/tmp/spec.tla', 2)
        ], 10).entries[0];

        let openedUri: vscode.Uri | undefined;
        let revealedRange: vscode.Range | undefined;
        const fakeDocument = {} as vscode.TextDocument;
        const fakeEditor = {
            selection: undefined as vscode.Selection | undefined,
            revealRange: (range: vscode.Range) => {
                revealedRange = range;
            }
        } as unknown as vscode.TextEditor;

        await revealCoverageEntry(entry, {
            openTextDocument: async (uri) => {
                openedUri = uri;
                return fakeDocument;
            },
            showTextDocument: async (document) => {
                assert.strictEqual(document, fakeDocument);
                return fakeEditor;
            }
        });

        assert.strictEqual(openedUri?.fsPath, '/tmp/spec.tla');
        assert.deepStrictEqual(revealedRange, entry.item.range);
        assert.ok((fakeEditor as { selection?: vscode.Selection }).selection instanceof vscode.Selection);
    });
});

function coverageItem(
    action: string,
    total: number,
    distinct: number,
    filePath = '/tmp/spec.tla',
    line = 0
): CoverageItem {
    return new CoverageItem('Spec', action, filePath, new vscode.Range(line, 0, line, 4), total, distinct);
}
