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

    let originalTla2tools: typeof import('../../../src/tla2tools') | undefined;
    let originalParseModule: typeof import('../../../src/commands/parseModule') | undefined;
    let originalExecuteCommand: typeof vscode.commands.executeCommand | undefined;
    let originalShowInformationMessage: typeof vscode.window.showInformationMessage | undefined;
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

    setup(() => {
        delete require.cache[checkModelPath];
        delete require.cache[tla2toolsPath];
        delete require.cache[parseModulePath];
    });

    teardown(() => {
        if (originalExecuteCommand) {
            (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
                .executeCommand = originalExecuteCommand;
        }
        if (originalShowInformationMessage) {
            (vscode.window as unknown as {
                showInformationMessage: typeof vscode.window.showInformationMessage
            }).showInformationMessage = originalShowInformationMessage;
        }
        if (originalShowWarningMessage) {
            (vscode.window as unknown as {
                showWarningMessage: typeof vscode.window.showWarningMessage
            }).showWarningMessage = originalShowWarningMessage;
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

    test('keeps the first URI-launched TLC run active and stoppable after a second request', async function() {
        this.timeout(5000);
        originalTla2tools = await import(tla2toolsPath);
        originalParseModule = await import(parseModulePath);

        class FakeProcess extends EventEmitter {
            stdout = new PassThrough();
            stderr = new PassThrough();
            killed = false;
        }

        const processes: FakeProcess[] = [];
        const processWaiters: Array<((process: FakeProcess) => void) | undefined> = [];
        const stopTargets: unknown[] = [];
        const waitForProcess = (index: number): Promise<FakeProcess> => processes[index]
            ? Promise.resolve(processes[index])
            : new Promise(resolve => { processWaiters[index] = resolve; });

        const stubbedTla2tools = {
            ...originalTla2tools,
            runTlc: async () => {
                const process = new FakeProcess();
                processes.push(process);
                processWaiters[processes.length - 1]?.(process);
                return {
                    commandLine: 'tlc',
                    process: process as unknown as import('child_process').ChildProcess,
                    mergedOutput: new PassThrough()
                };
            },
            stopProcess: (process: unknown) => { stopTargets.push(process); }
        } as typeof import('../../../src/tla2tools');
        require.cache[tla2toolsPath] = makeCacheEntry(tla2toolsPath, stubbedTla2tools);

        const stubbedParseModule = {
            ...originalParseModule,
            parseSpec: async () => new SanyData(),
        } as typeof import('../../../src/commands/parseModule');
        require.cache[parseModulePath] = makeCacheEntry(parseModulePath, stubbedParseModule);

        const contextValues: Record<string, unknown> = {};
        originalExecuteCommand = vscode.commands.executeCommand;
        (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
            .executeCommand = <T>(command: string, ...args: unknown[]): Thenable<T> => {
                if (command === 'setContext') {
                    contextValues[String(args[0])] = args[1];
                }
                return Promise.resolve(undefined as unknown as T);
            };

        originalShowInformationMessage = vscode.window.showInformationMessage;
        (vscode.window as unknown as {
            showInformationMessage: typeof vscode.window.showInformationMessage
        }).showInformationMessage = async () => undefined;
        originalShowWarningMessage = vscode.window.showWarningMessage;
        (vscode.window as unknown as {
            showWarningMessage: typeof vscode.window.showWarningMessage
        }).showWarningMessage = () => new Promise<undefined>(resolve => { void resolve; });

        const { checkModel, stopModelChecking, CTX_TLC_RUNNING, outChannel } = await import(checkModelPath);
        const originalBindTo = outChannel.bindTo;
        outChannel.bindTo = () => undefined;

        const tmpDir = await fsp.mkdtemp(path.join(os.tmpdir(), 'check-model-overlap-'));
        const longTla = path.join(tmpDir, 'Long.tla');
        const shortTla = path.join(tmpDir, 'Short.tla');
        const cfg = 'INIT Init\nNEXT Next\n';
        const module = (name: string) =>
            `---- MODULE ${name} ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\n====\n`;
        await fsp.writeFile(longTla, module('Long'));
        await fsp.writeFile(path.join(tmpDir, 'Long.cfg'), cfg);
        await fsp.writeFile(shortTla, module('Short'));
        await fsp.writeFile(path.join(tmpDir, 'Short.cfg'), cfg);

        const diagnostics = vscode.languages.createDiagnosticCollection('overlap-test');
        let longCheck: Promise<void> | undefined;
        let shortCheck: Promise<void> | undefined;
        let stopCompletion: Promise<void> | undefined;
        try {
            longCheck = checkModel(vscode.Uri.file(longTla), diagnostics, {} as vscode.ExtensionContext);
            const longProcess = await waitForProcess(0);
            const currentShortCheck = checkModel(
                vscode.Uri.file(shortTla), diagnostics, {} as vscode.ExtensionContext);
            shortCheck = currentShortCheck;
            const secondOutcome = await Promise.race([
                waitForProcess(1).then(process => ({ process })),
                currentShortCheck.then(() => ({ returned: true as const }))
            ]);
            if ('process' in secondOutcome) {
                secondOutcome.process.stdout.end();
                secondOutcome.process.emit('close', 0, null);
                await currentShortCheck;
            }

            stopCompletion = stopModelChecking().then(() => undefined);
            assert.deepStrictEqual(
                {
                    running: contextValues[CTX_TLC_RUNNING],
                    firstRunStopped: stopTargets.includes(longProcess)
                },
                { running: true, firstRunStopped: true },
                'Finishing the second URI-launched check must not hide or orphan the first run'
            );
        } finally {
            outChannel.bindTo = originalBindTo;
            for (const process of processes) {
                process.stdout.end();
                process.emit('close', 0, null);
            }
            await stopCompletion;
            await Promise.all([longCheck, shortCheck].filter((check): check is Promise<void> => !!check));
            diagnostics.dispose();
            await fsp.rm(tmpDir, { recursive: true, force: true });
        }
    });
});
