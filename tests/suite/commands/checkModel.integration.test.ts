import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { EventEmitter } from 'events';
import { PassThrough } from 'stream';
import { ChildProcess } from 'child_process';
import type { SpecFiles } from '../../../src/model/check';

const checkModel = require(path.resolve(
    __dirname,
    '../../../..',
    'out/src/commands/checkModel'
)) as typeof import('../../../src/commands/checkModel');

const tla2tools = require(path.resolve(
    __dirname,
    '../../../..',
    'out/src/tla2tools'
)) as typeof import('../../../src/tla2tools');

const { ToolProcessInfo } = tla2tools;

interface RunTlcCall {
    tlaFilePath: string;
    cfgFileName: string;
    showOptionsPrompt: boolean;
    extraOpts: string[];
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

    suiteSetup(async () => {
        const extension = vscode.extensions.getExtension(EXTENSION_ID);
        if (!extension) {
            throw new Error('TLA+ extension must be available during tests');
        }
        await extension.activate();
    });

    setup(async () => {
        await closeAllEditors();
    });

    teardown(async () => {
        await closeAllEditors();
    });

    test('runs TLC when matching model files exist', async () => {
    const specUri = vscode.Uri.file(path.join(modelSuiteRoot, 'Spec.tla'));
    const doc = await vscode.workspace.openTextDocument(specUri);
    await vscode.window.showTextDocument(doc);
    const directResult = await checkModel.getSpecFiles(specUri, true);
    console.log(`direct getSpecFiles: ${directResult?.cfgFilePath ?? 'undefined'}`);
    const { calls, restore: restoreRunTlc } = stubRunTlc();
    const { restore: restoreChannel } = stubOutChannel();
    const invocation = trackDoCheckModel();
    const specTracker = trackGetSpecFiles();
    await checkModel.getSpecFiles(specUri, true);
    console.log(`post-hook getSpecFiles result: ${specTracker.lastResult ? 'ok' : 'undefined'}`);

    try {
        await vscode.commands.executeCommand('tlaplus.model.check.run');
        console.log(`doCheckModel count: ${invocation.count}`);
        console.log(`getSpecFiles result: ${specTracker.lastResult ? 'ok' : 'undefined'}`);
        assert.strictEqual(calls.length, 1, 'Expected TLC to run once');
        assert.strictEqual(invocation.count, 1, 'doCheckModel should be invoked once');
        assert.ok(specTracker.lastResult, 'getSpecFiles should succeed');
        const [call] = calls;
        assert.strictEqual(path.basename(call.tlaFilePath), 'MCSpec.tla');
        assert.strictEqual(call.cfgFileName, 'MCSpec.cfg');
        assert.strictEqual(call.showOptionsPrompt, true);
    } finally {
        restoreRunTlc();
        restoreChannel();
        invocation.restore();
        specTracker.restore();
    }
    });

    test('shows warning and aborts when cfg is missing', async () => {
        const orphanUri = vscode.Uri.file(path.join(modelSuiteRoot, 'NoCfgSpec.tla'));
        const doc = await vscode.workspace.openTextDocument(orphanUri);
        await vscode.window.showTextDocument(doc);
        const { calls, restore: restoreRunTlc } = stubRunTlc();
        const warningStub = stubWarningMessages();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', orphanUri);
            assert.strictEqual(calls.length, 0, 'TLC should not run without a cfg file');
            assert.ok(
                warningStub.messages.some(m => m.includes('Model file NoCfgSpec.cfg')),
                'Missing cfg warning should be shown'
            );
        } finally {
            restoreRunTlc();
            warningStub.restore();
        }
    });

    test('custom run respects quick pick selection', async () => {
        const doc = await vscode.workspace.openTextDocument(path.join(modelSuiteRoot, 'Spec.tla'));
        await vscode.window.showTextDocument(doc);
        const quickPick = stubQuickPick('MCAltSpec.cfg');
        const { calls, restore: restoreRunTlc } = stubRunTlc();
        const { restore: restoreChannel } = stubOutChannel();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.customRun');
            assert.strictEqual(calls.length, 1, 'Custom run should launch TLC once');
            const [call] = calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'Spec.tla');
            assert.strictEqual(call.cfgFileName, 'MCAltSpec.cfg');
            assert.strictEqual(call.showOptionsPrompt, true);
            assert.ok(
                quickPick.lastItems?.includes('MCSpec.cfg') && quickPick.lastItems.includes('MCAltSpec.cfg'),
                'Quick pick should list available cfg files'
            );
        } finally {
            restoreRunTlc();
            restoreChannel();
            quickPick.restore();
        }
    });

    test('run again reuses last spec without prompting', async () => {
        const specUri = vscode.Uri.file(path.join(modelSuiteRoot, 'Spec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const { calls, restore: restoreRunTlc } = stubRunTlc();
        const { restore: restoreChannel } = stubOutChannel();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            await vscode.commands.executeCommand('tlaplus.model.check.runAgain');
            assert.strictEqual(calls.length, 2, 'Expected initial run plus runAgain');
            const second = calls[1];
            assert.strictEqual(second.showOptionsPrompt, false, 'runAgain should skip options prompt');
            assert.strictEqual(path.basename(second.tlaFilePath), 'MCSpec.tla');
        } finally {
            restoreRunTlc();
            restoreChannel();
        }
    });

   test('runs TLC against unsaved edits', async () => {
        const doc = await vscode.workspace.openTextDocument(path.join(modelSuiteRoot, 'MCAltSpec.tla'));
        const editor = await vscode.window.showTextDocument(doc);
        await editor.edit(builder => builder.insert(new vscode.Position(2, 0), '\\* unsaved change\n'));
        const { calls, restore: restoreRunTlc } = stubRunTlc();
        const { restore: restoreChannel } = stubOutChannel();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run');
            assert.strictEqual(calls.length, 1, 'Unsaved edits should not block TLC run');
            const [call] = calls;
            assert.strictEqual(path.basename(call.tlaFilePath), 'MCAltSpec.tla');
        } finally {
            restoreRunTlc();
            restoreChannel();
        }
    });

    test('merges tool stdout and stderr streams', async () => {
        const specUri = vscode.Uri.file(path.join(modelSuiteRoot, 'Spec.tla'));
        const doc = await vscode.workspace.openTextDocument(specUri);
        await vscode.window.showTextDocument(doc);
        const { calls, restore: restoreRunTlc } = stubRunTlc({
            returnProcess: true,
            stdout: '@!@!@STARTMSG 1000 @!@!@\n@!@!@ENDMSG 1000 @!@!@\n',
            stderr: 'tool-error-line\n'
        });
        const merged = captureOutChannelMergedOutput();

        try {
            await vscode.commands.executeCommand('tlaplus.model.check.run', specUri);
            assert.strictEqual(calls.length, 1, 'Process should launch once');
            assert.ok(
                merged.output.includes('@!@!@STARTMSG') && merged.output.includes('tool-error-line'),
                'Merged stream should contain stdout and stderr data'
            );
        } finally {
            restoreRunTlc();
            merged.restore();
        }
    });
});

function stubRunTlc(options: {
    returnProcess?: boolean;
    stdout?: string;
    stderr?: string;
} = {}) {
    const calls: RunTlcCall[] = [];
    const original = tla2tools.runTlc;
    const { returnProcess = false, stdout = '', stderr = '' } = options;

    (tla2tools as unknown as { runTlc: typeof tla2tools.runTlc }).runTlc = async (
        tlaFilePath: string,
        cfgFileName: string,
        showOptionsPrompt: boolean,
        extraOpts: string[] = [],
        extraJavaOpts: string[] = []
    ) => {
        console.log(`runTlc stub call for ${cfgFileName}`);
        calls.push({ tlaFilePath, cfgFileName, showOptionsPrompt, extraOpts });
        if (!returnProcess) {
            return undefined;
        }
        const proc = new MockChildProcess();
        const info = new ToolProcessInfo('tlc', proc as unknown as ChildProcess);
        setImmediate(() => {
            if (stdout) {
                proc.stdout.write(stdout);
            }
            proc.stdout.end();
            if (stderr) {
                proc.stderr.write(stderr);
            }
            proc.stderr.end();
            proc.emit('exit', 0);
            proc.emit('close', 0);
        });
        return info;
    };

    return {
        calls,
        restore: () => {
            (tla2tools as unknown as { runTlc: typeof tla2tools.runTlc }).runTlc = original;
        }
    };
}

function stubOutChannel() {
    const channel = checkModel.outChannel as unknown as { bindTo: typeof checkModel.outChannel.bindTo };
    const original = channel.bindTo;
    channel.bindTo = () => { /* no-op during tests */ };
    return {
        restore: () => {
            channel.bindTo = original;
        }
    };
}

function captureOutChannelMergedOutput() {
    const channel = checkModel.outChannel as unknown as { bindTo: typeof checkModel.outChannel.bindTo };
    const original = channel.bindTo;
    let output = '';
    channel.bindTo = (procInfo: InstanceType<typeof ToolProcessInfo>) => {
        procInfo.mergedOutput.on('data', (chunk: Buffer) => {
            output += chunk.toString();
        });
    };
    return {
        get output() {
            return output;
        },
        restore: () => {
            channel.bindTo = original;
        }
    };
}

function trackDoCheckModel() {
    const original = checkModel.doCheckModel;
    let count = 0;
    (checkModel as unknown as { doCheckModel: typeof checkModel.doCheckModel }).doCheckModel = async (
        specFiles,
        showCheckResultView,
        extContext,
        diagnostic,
        showOptionsPrompt,
        extraOpts,
        debuggerPortCallback
    ) => {
        count++;
        return original.call(
            checkModel,
            specFiles,
            showCheckResultView,
            extContext,
            diagnostic,
            showOptionsPrompt,
            extraOpts,
            debuggerPortCallback
        );
    };

    return {
        get count() {
            return count;
        },
        restore: () => {
            (checkModel as unknown as { doCheckModel: typeof checkModel.doCheckModel }).doCheckModel = original;
        }
    };
}

function trackGetSpecFiles() {
    const original = checkModel.getSpecFiles;
    let lastResult: SpecFiles | undefined;
    (checkModel as unknown as { getSpecFiles: typeof checkModel.getSpecFiles }).getSpecFiles = async (...args) => {
        console.log(`getSpecFiles called with warn=${args[1]} prefix=${args[2]}`);
        const result = await original(...args);
        lastResult = result ?? undefined;
        return result;
    };
    return {
        get lastResult(): SpecFiles | undefined {
            return lastResult;
        },
        restore: () => {
            (checkModel as unknown as { getSpecFiles: typeof checkModel.getSpecFiles }).getSpecFiles = original;
        }
    };
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
