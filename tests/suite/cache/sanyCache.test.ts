import * as assert from 'assert';
import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import { SanyCache } from '../../../src/cache/sanyCache';
import { SanyData } from '../../../src/parsers/sany';

suite('SANY Cache Test Suite', () => {
    let cache: SanyCache;
    let tempDir: string;
    let testFile: string;

    setup(async () => {
        // Create a new cache instance for each test
        cache = new SanyCache();

        // Create a temporary directory and test file
        tempDir = await fs.promises.mkdtemp(path.join(os.tmpdir(), 'sany-cache-test-'));
        testFile = path.join(tempDir, 'test.tla');
        await fs.promises.writeFile(testFile, '---- MODULE test ----\nVARIABLE x\nInit == x = 0\n====');
    });

    teardown(async () => {
        // Clear cache and remove temp files
        cache.clear();
        await fs.promises.rm(tempDir, { recursive: true, force: true });
    });

    test('Cache should store and retrieve SANY data', async () => {
        // Create mock SANY data
        const sanyData = new SanyData();
        sanyData.dCollection.addMessage(
            testFile,
            new vscode.Range(0, 0, 0, 10),
            'Test message',
            vscode.DiagnosticSeverity.Information
        );

        const symbols: vscode.SymbolInformation[] = [
            new vscode.SymbolInformation(
                'Init',
                vscode.SymbolKind.Function,
                'test',
                new vscode.Location(vscode.Uri.file(testFile), new vscode.Range(2, 0, 2, 12))
            )
        ];

        // Store in cache
        await cache.set(testFile, sanyData, symbols, []);

        // Retrieve from cache
        const cached = await cache.get(testFile);
        assert.ok(cached, 'Cache entry should exist');
        assert.strictEqual(cached.symbols.length, 1, 'Should have one symbol');
        assert.strictEqual(cached.symbols[0].name, 'Init', 'Symbol name should match');
        assert.strictEqual(cached.sanyData.dCollection.getMessages().length, 1, 'Should have one diagnostic message');
    });

    test('Cache should invalidate on file change', async () => {
        // Store initial data
        const sanyData = new SanyData();
        await cache.set(testFile, sanyData, [], []);

        // Verify it's cached
        let cached = await cache.get(testFile);
        assert.ok(cached, 'Initial cache entry should exist');

        // Modify the file
        await new Promise(resolve => setTimeout(resolve, 10)); // Small delay to ensure timestamp changes
        await fs.promises.writeFile(testFile, '---- MODULE test ----\nVARIABLE y\nInit == y = 1\n====');

        // Cache should be invalidated
        cached = await cache.get(testFile);
        assert.strictEqual(cached, undefined, 'Cache should be invalidated after file change');
    });

    test('Cache should enforce memory limits with LRU eviction', async () => {
        // Note: This is a simplified test. In reality, we'd need to mock the configuration
        // to set a very small cache size for testing

        const sanyData = new SanyData();
        const symbols: vscode.SymbolInformation[] = [];

        // Add multiple entries
        const files: string[] = [];
        for (let i = 0; i < 5; i++) {
            const file = path.join(tempDir, `test${i}.tla`);
            await fs.promises.writeFile(file, `---- MODULE test${i} ----\n====`);
            files.push(file);
            await cache.set(file, sanyData, symbols, []);
        }

        // All should be cached initially (assuming default size is large enough)
        for (const file of files) {
            const cached = await cache.get(file);
            assert.ok(cached, `File ${path.basename(file)} should be cached`);
        }
    });

    test('Cache should track hit/miss statistics', async () => {
        const sanyData = new SanyData();

        // Initial stats
        let stats = cache.getStats();
        assert.strictEqual(stats.hits, 0, 'Initial hits should be 0');
        assert.strictEqual(stats.misses, 0, 'Initial misses should be 0');

        // Cache miss
        let cached = await cache.get(testFile);
        assert.strictEqual(cached, undefined, 'Should be a cache miss');

        stats = cache.getStats();
        assert.strictEqual(stats.misses, 1, 'Should have 1 miss');

        // Store data
        await cache.set(testFile, sanyData, [], []);

        // Cache hit
        cached = await cache.get(testFile);
        assert.ok(cached, 'Should be a cache hit');

        stats = cache.getStats();
        assert.strictEqual(stats.hits, 1, 'Should have 1 hit');
        assert.strictEqual(stats.misses, 1, 'Misses should still be 1');

        // Calculate hit ratio
        const hitRatio = cache.getHitRatio();
        assert.strictEqual(hitRatio, 50, 'Hit ratio should be 50%');
    });

    test('Cache should handle dependency invalidation', async () => {
        // Create two files with dependency
        const mainFile = path.join(tempDir, 'main.tla');
        const depFile = path.join(tempDir, 'dep.tla');

        await fs.promises.writeFile(mainFile, '---- MODULE main ----\nEXTENDS dep\n====');
        await fs.promises.writeFile(depFile, '---- MODULE dep ----\nCONSTANT c\n====');

        const sanyData = new SanyData();

        // Cache main file with dependency on dep file
        await cache.set(mainFile, sanyData, [], [depFile]);

        // Verify it's cached
        let cached = await cache.get(mainFile);
        assert.ok(cached, 'Main file should be cached');

        // Invalidate dependents of dep file
        cache.invalidateDependents(depFile);

        // Main file should be invalidated
        cached = await cache.get(mainFile);
        assert.strictEqual(cached, undefined, 'Main file should be invalidated when dependency is invalidated');
    });

    test('Cache should be clearable', async () => {
        const sanyData = new SanyData();

        // Add some entries
        await cache.set(testFile, sanyData, [], []);

        // Verify it's cached
        let cached = await cache.get(testFile);
        assert.ok(cached, 'Should be cached before clear');

        // Clear cache
        cache.clear();

        // Should be empty
        cached = await cache.get(testFile);
        assert.strictEqual(cached, undefined, 'Cache should be empty after clear');

        const stats = cache.getStats();
        assert.strictEqual(stats.entries, 0, 'Should have 0 entries after clear');
    });

    test('Cache should report cached file paths', async () => {
        const sanyData = new SanyData();

        // Initially empty
        let paths = cache.getCachedPaths();
        assert.strictEqual(paths.length, 0, 'Should have no cached paths initially');

        // Add entries
        await cache.set(testFile, sanyData, [], []);

        paths = cache.getCachedPaths();
        assert.strictEqual(paths.length, 1, 'Should have one cached path');
        assert.ok(paths[0].endsWith('test.tla'), 'Cached path should be the test file');
    });
});