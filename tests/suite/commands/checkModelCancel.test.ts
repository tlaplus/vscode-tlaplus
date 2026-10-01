import * as assert from 'assert';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { EventEmitter } from 'events';
import { PassThrough } from 'stream';
import * as vscode from 'vscode';
import { SanyData } from '../../../src/parsers/sany';

suite('CheckModel command handling', () => {
    const fsp = fs.promises;
    const tla2toolsPath = require.resolve(path.resolve(__dirname, '../../../src/tla2tools'));
    const parseModulePath = require.resolve(path.resolve(__dirname, '../../../src/commands/parseModule'));
    const checkModelPath = require.resolve(path.resolve(__dirname, '../../../src/commands/checkModel'));
    const modelPath = require.resolve(path.resolve(__dirname, '../../../src/model/check'));
    const checkResultViewPath = require.resolve(path.resolve(__dirname, '../../../src/panels/checkResultView'));
    const debuggingPath = require.resolve(path.resolve(__dirname, '../../../src/debugger/debugging'));
    const modelResolverPath = require.resolve(path.resolve(__dirname, '../../../src/commands/modelResolver'));
    // Spec.tla with its model Spec.cfg, and the smoke test model SmokeSpec.
    const fixtureDir = path.resolve(__dirname, '../../../../tests/fixtures/checkModel');
    const fixtureSpec = path.join(fixtureDir, 'Spec.tla');
    const fixtureCfg = path.join(fixtureDir, 'Spec.cfg');
    const createOutFilesKey = 'tlaplus.tlc.modelChecker.createOutFiles';
    const delay = (ms: number) => new Promise<void>(resolve => setTimeout(resolve, ms));

    let originalTla2tools: typeof import('../../../src/tla2tools') | undefined;
    let originalParseModule: typeof import('../../../src/commands/parseModule') | undefined;
    let originalCheckResultView: typeof import('../../../src/panels/checkResultView') | undefined;
    let originalModelResolver: typeof import('../../../src/commands/modelResolver') | undefined;
    let originalExecuteCommand: typeof vscode.commands.executeCommand | undefined;
    let originalShowWarningMessage: typeof vscode.window.showWarningMessage | undefined;

    const makeCacheEntry = (filename: string, exports: unknown): NodeJS.Module => ({
        id: filename,
        filename,
        loaded: true,
        exports,
        parent: null,
        path: filename,
        paths: [],
        children: [],
        require,
        isPreloading: false,
    } as unknown as NodeJS.Module);

    // Checks of the fixture spec must not write .out files into the repository.
    suiteSetup(async () => {
        await vscode.workspace.getConfiguration().update(
            createOutFilesKey, false, vscode.ConfigurationTarget.Global);
    });

    suiteTeardown(async () => {
        await vscode.workspace.getConfiguration().update(
            createOutFilesKey, undefined, vscode.ConfigurationTarget.Global);
    });

    setup(() => {
        delete require.cache[debuggingPath];
        delete require.cache[checkModelPath];
        delete require.cache[tla2toolsPath];
        delete require.cache[parseModulePath];
    });

    teardown(() => {
        if (originalExecuteCommand) {
            (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
                .executeCommand = originalExecuteCommand;
        }
        if (originalShowWarningMessage) {
            (vscode.window as unknown as { showWarningMessage: typeof vscode.window.showWarningMessage })
                .showWarningMessage = originalShowWarningMessage;
            originalShowWarningMessage = undefined;
        }
        if (originalTla2tools) {
            require.cache[tla2toolsPath] = makeCacheEntry(tla2toolsPath, originalTla2tools);
        } else {
            delete require.cache[tla2toolsPath];
        }
        if (originalParseModule) {
            require.cache[parseModulePath] = makeCacheEntry(parseModulePath, originalParseModule);
        } else {
            delete require.cache[parseModulePath];
        }
        if (originalCheckResultView) {
            require.cache[checkResultViewPath] = makeCacheEntry(checkResultViewPath, originalCheckResultView);
            originalCheckResultView = undefined;
        }
        if (originalModelResolver) {
            require.cache[modelResolverPath] = makeCacheEntry(modelResolverPath, originalModelResolver);
            originalModelResolver = undefined;
        }
        delete require.cache[debuggingPath];
        delete require.cache[checkModelPath];
    });

    test('does not leave TLC running context when launch is cancelled', async function() {
        this.timeout(5000);
        originalTla2tools = await import(tla2toolsPath);
        originalParseModule = await import(parseModulePath);

        const stubbedTla2tools = {
            ...originalTla2tools,
            runTlc: async () => undefined,
        } as typeof import('../../../src/tla2tools');
        require.cache[tla2toolsPath] = makeCacheEntry(tla2toolsPath, stubbedTla2tools);

        // Stub parseSpec to avoid spawning Java SANY, which can exceed the
        // 5s timeout during cold JVM startup on Windows CI runners.
        const stubbedParseModule = {
            ...originalParseModule,
            parseSpec: async () => new SanyData(),
        } as typeof import('../../../src/commands/parseModule');
        require.cache[parseModulePath] = makeCacheEntry(parseModulePath, stubbedParseModule);

        const contextValues: Record<string, unknown> = {};
        originalExecuteCommand = vscode.commands.executeCommand;
        const stubExecuteCommand: typeof vscode.commands.executeCommand =
            <T>(command: string, ...rest: unknown[]): Thenable<T> => {
                if (command === 'setContext') {
                    const [key, value] = rest;
                    contextValues[String(key)] = value;
                }
                return Promise.resolve(undefined as unknown as T);
            };
        (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand }).executeCommand =
            stubExecuteCommand;

        const { doCheckModel, CTX_TLC_CAN_RUN_AGAIN, CTX_TLC_RUNNING } = await import(checkModelPath);
        const { SpecFiles } = await import(modelPath);

        const tmpDir = await fsp.mkdtemp(path.join(os.tmpdir(), 'check-model-cancel-'));
        const tlaFile = path.join(tmpDir, 'Dummy.tla');
        const cfgFile = path.join(tmpDir, 'Dummy.cfg');
        await fsp.writeFile(tlaFile, '---- MODULE Dummy ----\n====\n');
        await fsp.writeFile(cfgFile, 'SPECIFICATION Spec\n');

        const specFiles = new SpecFiles(tlaFile, cfgFile);
        const diagnostics = vscode.languages.createDiagnosticCollection('cancel-test');

        try {
            await doCheckModel(specFiles, true, {} as vscode.ExtensionContext, diagnostics, true);
        } finally {
            diagnostics.dispose();
            await fsp.rm(tmpDir, { recursive: true, force: true });
        }

        assert.strictEqual(
            contextValues[CTX_TLC_RUNNING],
            false,
            'TLC running context should be reset after cancellation'
        );
        assert.notStrictEqual(
            contextValues[CTX_TLC_CAN_RUN_AGAIN],
            true,
            'Run-again context must not be enabled when launch is cancelled'
        );
    });

    // To reproduce by hand:
    // 1. Open a .tla file whose model takes a while to check and run "TLA+: Check model with TLC".
    // 2. Close the "TLA+ model checking" tab while TLC is running.
    // 3. Run "TLA+: Check model with TLC" again. The warning "Another model checking process is
    //    currently running" appears with a "Show currently running process" button.
    // 4. Dismiss the warning with its close button or Escape, without clicking the button.
    // Before the fix, the "TLA+ model checking" tab reopened anyway.
    test('reveals the running check only when the warning\'s button is clicked', async () => {
        originalCheckResultView = await import(checkResultViewPath);
        let reveals = 0;
        require.cache[checkResultViewPath] = makeCacheEntry(checkResultViewPath, {
            ...originalCheckResultView,
            revealLastCheckResultView: () => { reveals++; }
        });
        let clicked = false;
        originalShowWarningMessage = vscode.window.showWarningMessage;
        (vscode.window as unknown as { showWarningMessage: (msg: string, button: string) => Thenable<unknown> })
            .showWarningMessage = (_msg, button) => Promise.resolve(clicked ? button : undefined);
        const { warnCheckRunning } = await import(checkModelPath);
        const tick = () => new Promise(resolve => setImmediate(resolve));

        warnCheckRunning({} as vscode.ExtensionContext);
        await tick();
        assert.strictEqual(reveals, 0);
        clicked = true;
        warnCheckRunning({} as vscode.ExtensionContext);
        await tick();
        assert.strictEqual(reveals, 1);
    });

    test('starts one TLC process when a second URI check arrives while the first runs', async function() {
        this.timeout(5000);
        originalTla2tools = await import(tla2toolsPath);
        originalParseModule = await import(parseModulePath);

        class FakeProcess extends EventEmitter {
            stdout = new PassThrough();
            stderr = new PassThrough();
        }

        // The first process runs until the test ends; any later one exits at
        // once, so that a check that wrongly starts TLC still returns.
        const spawned: FakeProcess[] = [];
        let onSpawn: () => void = () => undefined;
        const firstSpawned = new Promise<void>(resolve => { onSpawn = resolve; });
        const stubbedTla2tools = {
            ...originalTla2tools,
            runTlc: async () => {
                const process = new FakeProcess();
                spawned.push(process);
                if (spawned.length > 1) {
                    setImmediate(() => {
                        process.stdout.end();
                        process.emit('close', 0, null);
                    });
                }
                onSpawn();
                return {
                    commandLine: 'tlc',
                    process: process as unknown as import('child_process').ChildProcess,
                    mergedOutput: new PassThrough()
                };
            }
        } as typeof import('../../../src/tla2tools');
        require.cache[tla2toolsPath] = makeCacheEntry(tla2toolsPath, stubbedTla2tools);

        // Skip SANY, which is not under test.
        const stubbedParseModule = {
            ...originalParseModule,
            parseSpec: async () => new SanyData(),
        } as typeof import('../../../src/commands/parseModule');
        require.cache[parseModulePath] = makeCacheEntry(parseModulePath, stubbedParseModule);

        // Ignore context updates, and leave the "already running" warning
        // unanswered, as if the user has not clicked yet.
        originalExecuteCommand = vscode.commands.executeCommand;
        (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
            .executeCommand = <T>(): Thenable<T> => Promise.resolve(undefined as unknown as T);
        originalShowWarningMessage = vscode.window.showWarningMessage;
        (vscode.window as unknown as {
            showWarningMessage: typeof vscode.window.showWarningMessage
        }).showWarningMessage = () => new Promise<undefined>(resolve => { void resolve; });

        // Keep the fake output out of the TLC output channel.
        const { checkModel, outChannel } = await import(checkModelPath);
        const originalBindTo = outChannel.bindTo;
        outChannel.bindTo = () => undefined;

        // The fixture's only model is Spec.cfg, so getSpecFiles does not prompt.
        const tlaUri = vscode.Uri.file(fixtureSpec);
        const ctx = {} as vscode.ExtensionContext;
        const diagnostics = vscode.languages.createDiagnosticCollection('overlap-test');

        let first: Promise<void> | undefined;
        try {
            // Check the spec as Explorer does, wait for TLC to run, and check
            // it again.
            first = checkModel(tlaUri, diagnostics, ctx);
            await firstSpawned;
            await checkModel(tlaUri, diagnostics, ctx);
            assert.strictEqual(spawned.length, 1, 'A second URI check must not start another TLC process');
        } finally {
            // Let the first TLC exit so that its check returns.
            spawned[0]?.stdout.end();
            spawned[0]?.emit('close', 0, null);
            await first;
            outChannel.bindTo = originalBindTo;
            diagnostics.dispose();
        }
    });

    test('skips a smoke test quietly while a manual check is running', async function() {
        this.timeout(5000);
        originalTla2tools = await import(tla2toolsPath);
        originalParseModule = await import(parseModulePath);

        class FakeProcess extends EventEmitter {
            stdout = new PassThrough();
            stderr = new PassThrough();
        }

        // Every TLC process runs until the test ends it, and stopping one is
        // ignored.
        const spawned: FakeProcess[] = [];
        let onFirstSpawn: () => void = () => undefined;
        const firstSpawned = new Promise<void>(resolve => { onFirstSpawn = resolve; });
        let onSecondSpawn: () => void = () => undefined;
        const secondSpawned = new Promise<void>(resolve => { onSecondSpawn = resolve; });
        const stubbedTla2tools = {
            ...originalTla2tools,
            runTlc: async () => {
                const process = new FakeProcess();
                spawned.push(process);
                (spawned.length === 1 ? onFirstSpawn : onSecondSpawn)();
                return {
                    commandLine: 'tlc',
                    process: process as unknown as import('child_process').ChildProcess,
                    mergedOutput: new PassThrough()
                };
            },
            stopProcess: () => undefined
        } as typeof import('../../../src/tla2tools');
        require.cache[tla2toolsPath] = makeCacheEntry(tla2toolsPath, stubbedTla2tools);

        // Skip SANY, which is not under test.
        const stubbedParseModule = {
            ...originalParseModule,
            parseSpec: async () => new SanyData(),
        } as typeof import('../../../src/commands/parseModule');
        require.cache[parseModulePath] = makeCacheEntry(parseModulePath, stubbedParseModule);

        // Ignore context updates, and record every warning, leaving it
        // unanswered.
        originalExecuteCommand = vscode.commands.executeCommand;
        (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
            .executeCommand = <T>(): Thenable<T> => Promise.resolve(undefined as unknown as T);
        const warnings: string[] = [];
        originalShowWarningMessage = vscode.window.showWarningMessage;
        (vscode.window as unknown as {
            showWarningMessage: (message: string) => Thenable<undefined>
        }).showWarningMessage = (message: string) => {
            warnings.push(message);
            return new Promise<undefined>(resolve => { void resolve; });
        };

        // Keep the fake output out of the TLC output channel.
        const { doCheckModel, outChannel } = await import(checkModelPath);
        const { smokeTestSpec } = await import(debuggingPath);
        const { SpecFiles } = await import(modelPath);
        const originalBindTo = outChannel.bindTo;
        outChannel.bindTo = () => undefined;

        const ctx = {} as vscode.ExtensionContext;
        const diagnostics = vscode.languages.createDiagnosticCollection('smoke-test');

        let manual: Promise<unknown> | undefined;
        try {
            // Start a manual check of Spec, wait for TLC to run, and smoke test
            // Spec, which would check SmokeSpec.
            manual = doCheckModel(new SpecFiles(fixtureSpec, fixtureCfg), false, ctx, diagnostics, false);
            await firstSpawned;
            await smokeTestSpec(vscode.Uri.file(fixtureSpec), diagnostics, ctx);
            // smokeTestSpec does not await doCheckModel, so a wrongly started
            // TLC appears only after it returns.
            await Promise.race([secondSpawned, delay(500)]);
            assert.deepStrictEqual(
                { spawned: spawned.length, warnings },
                { spawned: 1, warnings: [] },
                'A smoke test must neither start TLC nor warn while a manual check runs'
            );
        } finally {
            // Let every TLC exit so that the manual check returns.
            for (const process of spawned) {
                process.stdout.end();
                process.emit('close', 0, null);
            }
            await manual;
            outChannel.bindTo = originalBindTo;
            diagnostics.dispose();
        }
    });

    test('rejects a URI check before resolving its model while a check is running', async function() {
        this.timeout(5000);
        originalTla2tools = await import(tla2toolsPath);
        originalParseModule = await import(parseModulePath);
        originalModelResolver = await import(modelResolverPath);

        class FakeProcess extends EventEmitter {
            stdout = new PassThrough();
            stderr = new PassThrough();
        }

        // The TLC process runs until the test ends it.
        let running: FakeProcess | undefined;
        let onSpawn: () => void = () => undefined;
        const spawned = new Promise<void>(resolve => { onSpawn = resolve; });
        const stubbedTla2tools = {
            ...originalTla2tools,
            runTlc: async () => {
                running = new FakeProcess();
                onSpawn();
                return {
                    commandLine: 'tlc',
                    process: running as unknown as import('child_process').ChildProcess,
                    mergedOutput: new PassThrough()
                };
            }
        } as typeof import('../../../src/tla2tools');
        require.cache[tla2toolsPath] = makeCacheEntry(tla2toolsPath, stubbedTla2tools);

        // Skip SANY, which is not under test.
        const stubbedParseModule = {
            ...originalParseModule,
            parseSpec: async () => new SanyData(),
        } as typeof import('../../../src/commands/parseModule');
        require.cache[parseModulePath] = makeCacheEntry(parseModulePath, stubbedParseModule);

        // Resolving a model may prompt the user to pick one; count the attempts.
        let resolves = 0;
        require.cache[modelResolverPath] = makeCacheEntry(modelResolverPath, {
            ...originalModelResolver,
            resolveModelForUri: async () => { resolves++; return undefined; }
        });

        // Ignore context updates, and leave the "already running" warning
        // unanswered, as if the user has not clicked yet.
        originalExecuteCommand = vscode.commands.executeCommand;
        (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
            .executeCommand = <T>(): Thenable<T> => Promise.resolve(undefined as unknown as T);
        originalShowWarningMessage = vscode.window.showWarningMessage;
        (vscode.window as unknown as {
            showWarningMessage: typeof vscode.window.showWarningMessage
        }).showWarningMessage = () => new Promise<undefined>(resolve => { void resolve; });

        // Keep the fake output out of the TLC output channel.
        const { checkModel, doCheckModel, outChannel } = await import(checkModelPath);
        const { SpecFiles } = await import(modelPath);
        const originalBindTo = outChannel.bindTo;
        outChannel.bindTo = () => undefined;

        const ctx = {} as vscode.ExtensionContext;
        const diagnostics = vscode.languages.createDiagnosticCollection('uri-reject-test');

        let first: Promise<unknown> | undefined;
        try {
            // Start a check and wait until doCheckModel has recorded its TLC
            // process, then check the spec as Explorer does.
            first = doCheckModel(new SpecFiles(fixtureSpec, fixtureCfg), false, ctx, diagnostics, false);
            await spawned;
            await new Promise(resolve => setImmediate(resolve));
            await checkModel(vscode.Uri.file(fixtureSpec), diagnostics, ctx);
            assert.strictEqual(resolves, 0, 'A rejected URI check must not resolve a model');
        } finally {
            // Let TLC exit so that the first check returns.
            running?.stdout.end();
            running?.emit('close', 0, null);
            await first;
            outChannel.bindTo = originalBindTo;
            diagnostics.dispose();
        }
    });

    test('restarts a smoke test once its previous TLC process has exited', async function() {
        this.timeout(5000);
        originalTla2tools = await import(tla2toolsPath);
        originalParseModule = await import(parseModulePath);

        class FakeProcess extends EventEmitter {
            stdout = new PassThrough();
            stderr = new PassThrough();
        }

        // Every TLC process runs until it is stopped, and, like a real
        // process, exits a little later.
        const spawned: FakeProcess[] = [];
        const spawnWaiters: (() => void)[] = [];
        const nthSpawn = (n: number) => new Promise<void>(resolve => {
            spawnWaiters[n] = resolve;
            if (spawned.length >= n) {
                resolve();
            }
        });
        const exit = (process: FakeProcess) => {
            process.stdout.end();
            process.emit('close', 0, null);
        };
        const stubbedTla2tools = {
            ...originalTla2tools,
            runTlc: async () => {
                const process = new FakeProcess();
                spawned.push(process);
                spawnWaiters[spawned.length]?.();
                return {
                    commandLine: 'tlc',
                    process: process as unknown as import('child_process').ChildProcess,
                    mergedOutput: new PassThrough()
                };
            },
            stopProcess: (process: FakeProcess) => { setTimeout(() => exit(process), 20); }
        } as unknown as typeof import('../../../src/tla2tools');
        require.cache[tla2toolsPath] = makeCacheEntry(tla2toolsPath, stubbedTla2tools);

        // Skip SANY, which is not under test.
        const stubbedParseModule = {
            ...originalParseModule,
            parseSpec: async () => new SanyData(),
        } as typeof import('../../../src/commands/parseModule');
        require.cache[parseModulePath] = makeCacheEntry(parseModulePath, stubbedParseModule);

        // Ignore context updates, and record every warning, leaving it
        // unanswered.
        originalExecuteCommand = vscode.commands.executeCommand;
        (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
            .executeCommand = <T>(): Thenable<T> => Promise.resolve(undefined as unknown as T);
        const warnings: string[] = [];
        originalShowWarningMessage = vscode.window.showWarningMessage;
        (vscode.window as unknown as {
            showWarningMessage: (message: string) => Thenable<undefined>
        }).showWarningMessage = (message: string) => {
            warnings.push(message);
            return new Promise<undefined>(resolve => { void resolve; });
        };

        // Keep the fake output out of the TLC output channel.
        const { outChannel } = await import(checkModelPath);
        const { smokeTestSpec } = await import(debuggingPath);
        const originalBindTo = outChannel.bindTo;
        outChannel.bindTo = () => undefined;

        const ctx = {} as vscode.ExtensionContext;
        const diagnostics = vscode.languages.createDiagnosticCollection('smoke-restart-test');
        const spec = vscode.Uri.file(fixtureSpec);

        try {
            // Smoke test Spec, wait until its TLC process is recorded, and
            // smoke test Spec again, which stops the first run.
            await smokeTestSpec(spec, diagnostics, ctx);
            await nthSpawn(1);
            await new Promise(resolve => setImmediate(resolve));
            await smokeTestSpec(spec, diagnostics, ctx);
            await Promise.race([nthSpawn(2), delay(500)]);
            assert.deepStrictEqual(
                { spawned: spawned.length, warnings },
                { spawned: 2, warnings: [] },
                'A smoke test must replace its previous run once that run has exited'
            );
        } finally {
            for (const process of spawned) {
                exit(process);
            }
            outChannel.bindTo = originalBindTo;
            diagnostics.dispose();
        }
    });
});
