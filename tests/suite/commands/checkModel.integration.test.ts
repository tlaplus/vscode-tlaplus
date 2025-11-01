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

    type ExtensionApi = {
        setTlcRunner: (runner: TlcRunner) => void;
        resetTlcRunner: () => void;
    };

    let extensionApi: ExtensionApi;
    let previousCreateOutFiles: boolean | undefined;

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
    });

    setup(async () => {
        await closeAllEditors();
        const config = vscode.workspace.getConfiguration();
        previousCreateOutFiles = config.get<boolean>('tlaplus.tlc.modelChecker.createOutFiles') ?? undefined;
        await config.update(
            'tlaplus.tlc.modelChecker.createOutFiles',
            false,
            vscode.ConfigurationTarget.Global
        );
        extensionApi.resetTlcRunner();
    });

    teardown(async () => {
        extensionApi.resetTlcRunner();
        const config = vscode.workspace.getConfiguration();
        await config.update(
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
        const stub = stubRunTlc();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            assert.strictEqual(stub.calls.length, 1, 'Expected TLC to run once');
            const [call] = stub.calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'MCSpec.tla');
            assert.strictEqual(call.cfgFileName, 'MCSpec.cfg');
            assert.strictEqual(call.showOptionsPrompt, true);
        } finally {
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
