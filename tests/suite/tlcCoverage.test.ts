import * as assert from 'assert';
import * as vscode from 'vscode';
import { TlcCoverageDecorationProvider } from '../../src/tlcCoverage';

suite('TLC Coverage Settings', () => {
    const enabledKey = 'tlaplus.tlc.profiler.enabled';
    const thresholdsKey = 'tlaplus.tlc.profiler.thresholds';
    const config = vscode.workspace.getConfiguration();
    let originalEnabled: boolean | undefined;
    let originalThresholds: unknown;

    suiteSetup(() => {
        originalEnabled = config.inspect<boolean>(enabledKey)?.globalValue;
        originalThresholds = config.inspect(thresholdsKey)?.globalValue;
    });

    suiteTeardown(async () => {
        await config.update(enabledKey, originalEnabled, vscode.ConfigurationTarget.Global);
        await config.update(thresholdsKey, originalThresholds as unknown, vscode.ConfigurationTarget.Global);
    });

    function getLevelByName(provider: TlcCoverageDecorationProvider, name: string) {
        const levels = (provider as unknown as { coverageLevels: Array<{ name: string; minInvocations: number; maxInvocations: number }> })
            .coverageLevels;
        const level = levels.find(entry => entry.name === name);
        assert.ok(level, `Missing coverage level ${name}`);
        return level!;
    }

    test('applies enabled setting on construction', async () => {
        await config.update(enabledKey, true, vscode.ConfigurationTarget.Global);
        const provider = new TlcCoverageDecorationProvider({} as vscode.ExtensionContext);
        try {
            assert.strictEqual(provider.isEnabled(), true);
        } finally {
            provider.dispose();
        }
    });

    test('uses configured thresholds for absolute coverage levels', async () => {
        await config.update(
            thresholdsKey,
            { rare: 1, low: 2, medium: 3, high: 4 },
            vscode.ConfigurationTarget.Global
        );
        const provider = new TlcCoverageDecorationProvider({} as vscode.ExtensionContext);
        try {
            const rare = getLevelByName(provider, 'rare');
            const low = getLevelByName(provider, 'low');
            const medium = getLevelByName(provider, 'medium');
            const high = getLevelByName(provider, 'high');
            const hot = getLevelByName(provider, 'hot');

            assert.strictEqual(rare.minInvocations, 1);
            assert.strictEqual(rare.maxInvocations, 1);
            assert.strictEqual(low.minInvocations, 2);
            assert.strictEqual(low.maxInvocations, 2);
            assert.strictEqual(medium.minInvocations, 3);
            assert.strictEqual(medium.maxInvocations, 3);
            assert.strictEqual(high.minInvocations, 4);
            assert.strictEqual(high.maxInvocations, 4);
            assert.strictEqual(hot.minInvocations, 5);
        } finally {
            provider.dispose();
        }
    });

    test('falls back to defaults when thresholds are invalid', async () => {
        await config.update(
            thresholdsKey,
            { rare: 10, low: 5, medium: 1000, high: 10000 },
            vscode.ConfigurationTarget.Global
        );
        const provider = new TlcCoverageDecorationProvider({} as vscode.ExtensionContext);
        try {
            const rare = getLevelByName(provider, 'rare');
            const low = getLevelByName(provider, 'low');
            const medium = getLevelByName(provider, 'medium');
            const high = getLevelByName(provider, 'high');
            const hot = getLevelByName(provider, 'hot');

            assert.strictEqual(rare.minInvocations, 1);
            assert.strictEqual(rare.maxInvocations, 10);
            assert.strictEqual(low.minInvocations, 11);
            assert.strictEqual(low.maxInvocations, 100);
            assert.strictEqual(medium.minInvocations, 101);
            assert.strictEqual(medium.maxInvocations, 1000);
            assert.strictEqual(high.minInvocations, 1001);
            assert.strictEqual(high.maxInvocations, 10000);
            assert.strictEqual(hot.minInvocations, 10001);
        } finally {
            provider.dispose();
        }
    });

    test('emits enabled change when configuration updates', async () => {
        await config.update(enabledKey, false, vscode.ConfigurationTarget.Global);
        const provider = new TlcCoverageDecorationProvider({} as vscode.ExtensionContext);
        try {
            const enabledPromise = new Promise<boolean>((resolve, reject) => {
                const timeout = setTimeout(() => reject(new Error('Timed out waiting for enabled event')), 2000);
                const disposable = provider.onDidChangeEnabled(value => {
                    clearTimeout(timeout);
                    disposable.dispose();
                    resolve(value);
                });
            });

            await config.update(enabledKey, true, vscode.ConfigurationTarget.Global);
            const value = await enabledPromise;
            assert.strictEqual(value, true);
            assert.strictEqual(provider.isEnabled(), true);
        } finally {
            provider.dispose();
        }
    });
});
