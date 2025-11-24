import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { EventEmitter } from 'events';
import { PassThrough } from 'stream';
import { ChildProcess } from 'child_process';
import { promises as fs } from 'fs';

type CheckModelModule = typeof import('../../../src/commands/checkModel');
type TlcRunner = Parameters<CheckModelModule['setTlcRunner']>[0];
type ToolProcessInfoLike = Exclude<Awaited<ReturnType<TlcRunner>>, undefined>;

interface RunTlcCall {
    tlaFilePath: string;
    cfgFileName: string;
    showOptionsPrompt: boolean;
    extraOpts: string[];
    extraJavaOpts: string[];
}

class MockChildProcess extends EventEmitter {
    public stdout: PassThrough;
    public stderr: PassThrough;
    public killed = false;

    constructor() {
        super();
        this.stdout = new PassThrough();
        this.stderr = new PassThrough();
    }

    kill(_signal?: NodeJS.Signals | number): boolean {
        this.killed = true;
        this.emit('close', -1);
        return true;
    }
}

suite('Model check command integration', () => {
    const EXTENSION_ID = 'tlaplus.vscode-ide';
    const modelSuiteRoot = path.resolve(
        __dirname,
        '../../../../tests/fixtures/workspaces/model-suite'
    );
    const matrixRoot = path.resolve(
        __dirname,
        '../../../../tests/fixtures/workspaces/model-matrix'
    );
    const renamedRoot = path.join(matrixRoot, 'renamed');
    const instanceRoot = path.join(matrixRoot, 'instance');
    const libraryRoot = path.join(matrixRoot, 'library');
    const libraryDepsRoot = path.join(libraryRoot, 'deps');
    const mismatchRoot = path.join(matrixRoot, 'mismatch');
    const multiRootBase = path.resolve(
        __dirname,
        '../../../../tests/fixtures/workspaces/multi-root'
    );

    type ExtensionApi = {
        setTlcRunner: (runner: TlcRunner) => void;
        resetTlcRunner: () => void;
    };

    let extensionApi: ExtensionApi;
    let previousCreateOutFiles: boolean | undefined;
    let checkModelModule: CheckModelModule;

    suiteSetup(async () => {
        const extension = vscode.extensions.getExtension(EXTENSION_ID);
        if (!extension) {
            throw new Error('TLA+ extension should be available during tests');
        }
        const exports = await extension.activate() as ExtensionApi | undefined;
        if (!exports || typeof exports.setTlcRunner !== 'function') {
            throw new Error('Extension did not expose TLC runner override API');
        }
        extensionApi = exports;
        checkModelModule = await import('../../../src/commands/checkModel');
    });

    setup(async () => {
        await closeAllEditors();
        const config = vscode.workspace.getConfiguration();
        previousCreateOutFiles = config.get<boolean>('tlaplus.tlc.modelChecker.createOutFiles') ?? undefined;
        await updateConfig(
            'tlaplus.tlc.modelChecker.createOutFiles',
            false,
            vscode.ConfigurationTarget.Global
        );
        extensionApi.resetTlcRunner();
    });

    teardown(async () => {
        extensionApi.resetTlcRunner();
        await updateConfig(
            'tlaplus.tlc.modelChecker.createOutFiles',
            previousCreateOutFiles,
            vscode.ConfigurationTarget.Global
        );
        previousCreateOutFiles = undefined;
        await deleteIfExists(path.join(modelSuiteRoot, 'MCSpec.out'));
        await deleteIfExists(path.join(modelSuiteRoot, 'MCAltSpec.out'));
        await closeAllEditors();
    });

    test('runs TLC when matching model files exist', async () => {
        const specUri = vscode.Uri.file(path.join(modelSuiteRoot, 'Spec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const sampleOutputPath = path.resolve(
            __dirname,
            '../../../../tests/fixtures/parsers/tlc/override-stdout.out'
        );
        const sampleOutput = await fs.readFile(sampleOutputPath, 'utf8');
        const stub = stubRunTlc({
            returnProcess: true,
            stdout: sampleOutput
        });

        const originalExecuteCommand = vscode.commands.executeCommand;
        const contextCalls: Array<{ key: unknown; value: unknown }> = [];
        (vscode.commands.executeCommand as unknown) = (async (command: string, ...args: unknown[]) => {
            if (command === 'setContext') {
                contextCalls.push({ key: args[0], value: args[1] });
            }
            return originalExecuteCommand(command, ...args);
        }) as typeof vscode.commands.executeCommand;

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            await stub.waitForMerged();
            assert.strictEqual(stub.calls.length, 1, 'Expected TLC to run once');
            const [call] = stub.calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'MCSpec.tla');
            assert.strictEqual(call.cfgFileName, 'MCSpec.cfg');
            assert.strictEqual(call.showOptionsPrompt, true);

            const canRunAgainCalls = contextCalls
                .filter(c => c.key === 'tlaplus.tlc.canRunAgain')
                .map(c => c.value);
            assert.deepStrictEqual(canRunAgainCalls, [true], 'Expected TLC runAgain context to be enabled');

            const runningStates = contextCalls
                .filter(c => c.key === 'tlaplus.tlc.isRunning')
                .map(c => c.value);
            assert.ok(runningStates.includes(true), 'Expected TLC running context to be set');
            assert.ok(runningStates.includes(false), 'Expected TLC running context to be cleared');
        } finally {
            (vscode.commands.executeCommand as unknown) = originalExecuteCommand;
            stub.restore();
        }
    });

    test('shows warning and aborts when cfg is missing', async () => {
        const orphanUri = vscode.Uri.file(path.join(modelSuiteRoot, 'NoCfgSpec.tla'));
        const doc = await vscode.workspace.openTextDocument(orphanUri);
        await vscode.window.showTextDocument(doc);
        const stub = stubRunTlc();
        const warningStub = stubWarningMessages();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', orphanUri);
            assert.strictEqual(stub.calls.length, 0, 'TLC should not run without a cfg file');
            assert.ok(
                warningStub.messages.some(m => m.includes('Model file NoCfgSpec.cfg')),
                'Missing cfg warning should be shown'
            );
        } finally {
            stub.restore();
            warningStub.restore();
        }
    });

    test('custom run respects quick pick selection', async () => {
        const doc = await vscode.workspace.openTextDocument(path.join(modelSuiteRoot, 'Spec.tla'));
        await vscode.window.showTextDocument(doc);
        const quickPick = stubQuickPick('MCAltSpec.cfg');
        const stub = stubRunTlc();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.customRun');
            assert.strictEqual(stub.calls.length, 1, 'Custom run should launch TLC once');
            const [call] = stub.calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'Spec.tla');
            assert.strictEqual(call.cfgFileName, 'MCAltSpec.cfg');
            assert.strictEqual(call.showOptionsPrompt, true);
            assert.ok(
                quickPick.lastItems?.includes('MCSpec.cfg') &&
                quickPick.lastItems.includes('MCAltSpec.cfg'),
                'Quick pick should list available cfg files'
            );
        } finally {
            stub.restore();
            quickPick.restore();
        }
    });

    test('run again reuses last spec without prompting', async () => {
        const specUri = vscode.Uri.file(path.join(modelSuiteRoot, 'Spec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const stub = stubRunTlc();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            await vscode.commands.executeCommand('tlaplus.model.check.runAgain');
            assert.strictEqual(stub.calls.length, 2, 'Expected initial run plus runAgain');
            const [, second] = stub.calls;
            assert.strictEqual(second.showOptionsPrompt, false, 'runAgain should skip options prompt');
            assert.strictEqual(path.basename(second.tlaFilePath), 'MCSpec.tla');
        } finally {
            stub.restore();
        }
    });

    test('runs TLC against unsaved edits', async () => {
        const doc = await vscode.workspace.openTextDocument(path.join(modelSuiteRoot, 'MCAltSpec.tla'));
        const editor = await vscode.window.showTextDocument(doc);
        await editor.edit(builder => builder.insert(new vscode.Position(2, 0), '\\* unsaved change\n'));
        const stub = stubRunTlc();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run');
            assert.strictEqual(stub.calls.length, 1, 'Unsaved edits should not block TLC run');
            const [call] = stub.calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'MCAltSpec.tla');
        } finally {
            stub.restore();
        }
    });

    test('respects SPECIFICATION override in cfg files', async () => {
        const specUri = vscode.Uri.file(path.join(renamedRoot, 'RenamedSpec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const stub = stubRunTlc();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            assert.strictEqual(stub.calls.length, 1, 'Expected TLC to run once with SPECIFICATION override');
            const [call] = stub.calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'MCRenamedSpec.tla');
            assert.strictEqual(call.cfgFileName, 'MCRenamedSpec.cfg');
        } finally {
            stub.restore();
        }
    });

    test('runs TLC when module search paths include external libraries', async () => {
        const specUri = vscode.Uri.file(path.join(libraryRoot, 'LibrarySpec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const config = vscode.workspace.getConfiguration();
        const previousModuleSearchPaths =
            config.get<string[]>('tlaplus.moduleSearchPaths') ?? undefined;
        await updateConfig(
            'tlaplus.moduleSearchPaths',
            [libraryDepsRoot],
            vscode.ConfigurationTarget.Global
        );
        const stub = stubRunTlc();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            assert.strictEqual(stub.calls.length, 1, 'Expected TLC to run once with library path override');
            const [call] = stub.calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'MCLibrarySpec.tla');
        } finally {
            stub.restore();
            await updateConfig(
                'tlaplus.moduleSearchPaths',
                previousModuleSearchPaths,
                vscode.ConfigurationTarget.Global
            );
        }
    });

    test('accepts models that INSTANCE the spec module', async () => {
        const specUri = vscode.Uri.file(path.join(instanceRoot, 'Counter.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const stub = stubRunTlc();
        const warningStub = stubWarningMessages();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            assert.strictEqual(stub.calls.length, 1, 'INSTANCE-based model should start TLC');
            const [call] = stub.calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'MCCounter.tla');
            assert.strictEqual(path.basename(call.cfgFileName), 'MCCounter.cfg');
            assert.deepStrictEqual(warningStub.messages, [], 'INSTANCE model should not raise warnings');
        } finally {
            stub.restore();
            warningStub.restore();
        }
    });

    test('supports multi-root workspaces when model checking', async () => {
        const primaryRoot = path.join(multiRootBase, 'rootPrimary');
        const specUri = vscode.Uri.file(path.join(primaryRoot, 'SpecMulti.tla'));
        const specFiles = await checkModelModule.getSpecFiles(specUri);
        assert.ok(specFiles, 'Expected spec files to be resolved for multi-root workspace');
        if (!specFiles) {
            return;
        }
        assert.strictEqual(path.basename(specFiles.tlaFilePath), 'MCSpecMulti.tla');
        assert.strictEqual(path.basename(specFiles.cfgFilePath), 'MCSpecMulti.cfg');
    });

    test('skips TLC when model extends a mismatched module', async () => {
        const specUri = vscode.Uri.file(path.join(mismatchRoot, 'MismatchSpec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const stub = stubRunTlc();
        const warningStub = stubWarningMessages();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            assert.strictEqual(stub.calls.length, 0, 'Mismatched model should not start TLC');
            assert.ok(
                warningStub.messages.some(msg => msg.includes('does not reference MismatchSpec')),
                'Mismatch warning should mention missing reference'
            );
        } finally {
            stub.restore();
            warningStub.restore();
        }
    });

    test('merges tool stdout and stderr streams', async () => {
        const specUri = vscode.Uri.file(path.join(modelSuiteRoot, 'Spec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const stub = stubRunTlc({
            returnProcess: true,
            stdout: '@!@!@STARTMSG 1000 @!@!@\n@!@!@ENDMSG 1000 @!@!@\n*** Errors: 1\n',
            stderr: 'tool-error-line\n'
        });

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            assert.strictEqual(stub.calls.length, 1, 'Process should launch once');
            await stub.waitForMerged();
            assert.ok(
                stub.mergedOutput.includes('tool-error-line') &&
                stub.mergedOutput.includes('@!@!@STARTMSG'),
                'Merged stream should contain stdout and stderr data'
            );
        } finally {
            stub.restore();
        }
    });

function stubRunTlc(options: {
    returnProcess?: boolean;
    stdout?: string;
    stderr?: string;
} = {}) {
    const calls: RunTlcCall[] = [];
    let mergedBuffer = '';
    const { returnProcess = false, stdout = '', stderr = '' } = options;
    let mergedResolve: (() => void) | undefined;
    const mergedCompleted = new Promise<void>(resolve => {
        mergedResolve = resolve;
    });
    if (!returnProcess) {
        mergedResolve?.();
    }

    const runner: TlcRunner = async (
        tlaFilePath: string,
        cfgFileName: string,
        showOptionsPrompt: boolean,
        extraOpts: string[] = [],
        extraJavaOpts: string[] = []
    ) => {
        calls.push({ tlaFilePath, cfgFileName, showOptionsPrompt, extraOpts, extraJavaOpts });
        if (!returnProcess) {
            return undefined;
        }

        const process = new MockChildProcess();
        const mergedOutput = new PassThrough();
        process.stdout.pipe(mergedOutput, { end: false });
        process.stderr.pipe(mergedOutput, { end: false });
        process.on('close', () => mergedOutput.end());
        mergedOutput.on('data', chunk => {
            mergedBuffer += chunk.toString();
        });
        mergedOutput.on('end', () => {
            mergedResolve?.();
        });

        setImmediate(() => {
            if (stdout) {
                process.stdout.write(stdout);
            }
            process.stdout.end();
            if (stderr) {
                process.stderr.write(stderr);
            }
            process.stderr.end();
            process.emit('exit', 0);
            process.emit('close', 0);
        });

        const info: ToolProcessInfoLike = {
            commandLine: 'tlc',
            process: process as unknown as ChildProcess,
            mergedOutput
        };
        return info;
    };

    extensionApi.setTlcRunner(runner);

    return {
        calls,
        get mergedOutput(): string {
            return mergedBuffer;
        },
        async waitForMerged(): Promise<void> {
            await mergedCompleted;
        },
        restore: () => extensionApi.resetTlcRunner()
    };
}
});

async function updateConfig(
    setting: string,
    value: unknown,
    target: vscode.ConfigurationTarget
): Promise<void> {
    const config = vscode.workspace.getConfiguration();
    const previousValue = config.get(setting);
    if (areConfigValuesEqual(previousValue, value)) {
        await config.update(setting, value, target);
        return;
    }
    await new Promise<void>((resolve, reject) => {
        const disposable = vscode.workspace.onDidChangeConfiguration(event => {
            if (event.affectsConfiguration(setting)) {
                disposable.dispose();
                resolve();
            }
        });
        config.update(setting, value, target).then(
            () => { /* wait for event */ },
            err => {
                disposable.dispose();
                reject(err);
            }
        );
    });
}

function areConfigValuesEqual(a: unknown, b: unknown): boolean {
    return JSON.stringify(a) === JSON.stringify(b);
}

function stubWarningMessages() {
    const original = vscode.window.showWarningMessage;
    const messages: string[] = [];

    (vscode.window.showWarningMessage as unknown) = ((message: string, ..._items: unknown[]) => {
        messages.push(message);
        return Promise.resolve(undefined);
    }) as typeof vscode.window.showWarningMessage;

    return {
        messages,
        restore: () => {
            (vscode.window.showWarningMessage as unknown) = original;
        }
    };
}

function stubQuickPick(selection: string) {
    const original = vscode.window.showQuickPick;
    let lastItems: readonly string[] | undefined;

    (vscode.window.showQuickPick as unknown) = ((
        items: readonly string[] | Thenable<readonly string[]>,
        ..._rest: unknown[]
    ) => {
        if (Array.isArray(items)) {
            lastItems = items;
        }
        return Promise.resolve(selection);
    }) as unknown as typeof vscode.window.showQuickPick;

    return {
        get lastItems() {
            return lastItems;
        },
        restore: () => {
            (vscode.window.showQuickPick as unknown) = original;
        }
    };
}

async function closeAllEditors(): Promise<void> {
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
}

async function deleteIfExists(fsPath: string): Promise<void> {
    try {
        await fs.unlink(fsPath);
    } catch (err) {
        const error = err as NodeJS.ErrnoException;
        if (error.code !== 'ENOENT') {
            throw err;
        }
    }
}
