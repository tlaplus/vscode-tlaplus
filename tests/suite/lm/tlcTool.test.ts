import * as assert from 'assert';
import * as fsp from 'fs/promises';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { CheckModuleTool, FileParameter } from '../../../src/lm/TLCTool';
import * as checkModel from '../../../src/commands/checkModel';
import * as common from '../../../src/common';
import * as tla2tools from '../../../src/tla2tools';
import { SpecFiles } from '../../../src/model/check';
import { LanguageModelToolInvocationOptions } from 'vscode';
import { EventEmitter } from 'events';
import { ToolProcessInfo } from '../../../src/tla2tools';
import { ChildProcess } from 'child_process';

class MockStdout extends EventEmitter {
    public on(event: string | symbol, listener: (...args: unknown[]) => void): this {
        return super.on(event, listener);
    }
}

class MockProcess extends EventEmitter {
    public stdout = new MockStdout();
    public stderr = new MockStdout();
    public killed = false;

    kill(): boolean {
        this.killed = true;
        this.emit('killed');
        return true;
    }
}

suite('TLC Tool cancellation handling', () => {
    test('CheckModuleTool rejects missing input file', async () => {
        const checkModelMutable = checkModel as unknown as {
            getSpecFiles: typeof checkModel.getSpecFiles;
        };
        const commonMutable = common as unknown as {
            exists: typeof common.exists;
        };
        const originalGetSpecFiles = checkModelMutable.getSpecFiles;
        const originalExists = commonMutable.exists;
        let getSpecFilesCalled = 0;

        checkModelMutable.getSpecFiles = async () => {
            getSpecFilesCalled++;
            return undefined;
        };
        commonMutable.exists = async () => false;

        try {
            const tool = new CheckModuleTool();
            const cts = new vscode.CancellationTokenSource();

            const filePath = path.join(__dirname, 'Missing.tla');
            const options = {
                toolInvocationToken: undefined,
                input: {
                    fileName: filePath
                }
            } as unknown as LanguageModelToolInvocationOptions<FileParameter>;

            const result = await tool.invoke(options, cts.token);
            assert.strictEqual(getSpecFilesCalled, 0, 'getSpecFiles should not run when file is missing');
            assert.strictEqual(result.content.length, 1);
            const [part] = result.content;
            assert.ok(part instanceof vscode.LanguageModelTextPart, 'Result should be a text part');
            assert.strictEqual((part as vscode.LanguageModelTextPart).value,
                `File ${filePath} does not exist`);
        } finally {
            checkModelMutable.getSpecFiles = originalGetSpecFiles;
            commonMutable.exists = originalExists;
        }
    });

    test('CheckModuleTool respects pre-cancelled token', async () => {
        const checkModelMutable = checkModel as unknown as {
            getSpecFiles: typeof checkModel.getSpecFiles;
        };
        const originalGetSpecFiles = checkModelMutable.getSpecFiles;
        let getSpecFilesCalled = 0;
        checkModelMutable.getSpecFiles = async () => {
            getSpecFilesCalled++;
            return undefined;
        };

        try {
            const tool = new CheckModuleTool();
            const cts = new vscode.CancellationTokenSource();
            cts.cancel();

            const filePath = path.join(__dirname, 'Sample.tla');
            const options = {
                toolInvocationToken: undefined,
                input: {
                    fileName: filePath
                }
            } as unknown as LanguageModelToolInvocationOptions<FileParameter>;

            const result = await tool.invoke(options, cts.token);
            assert.strictEqual(getSpecFilesCalled, 0, 'getSpecFiles should not run when already cancelled');
            assert.strictEqual(result.content.length, 1, 'Expected single cancellation message');
            const [part] = result.content;
            assert.ok(part instanceof vscode.LanguageModelTextPart, 'Result should be a text part');
            assert.strictEqual((part as vscode.LanguageModelTextPart).value,
                `Model checking cancelled for ${filePath}.`);
        } finally {
            checkModelMutable.getSpecFiles = originalGetSpecFiles;
        }
    });

    test('CheckModuleTool cancels an in-flight TLC process', async () => {
        const checkModelMutable = checkModel as unknown as {
            getSpecFiles: typeof checkModel.getSpecFiles;
            mapTlcOutputLine: typeof checkModel.mapTlcOutputLine;
            outChannel: typeof checkModel.outChannel;
        };
        const commonMutable = common as unknown as {
            exists: typeof common.exists;
        };
        const tla2toolsMutable = tla2tools as unknown as {
            runTlc: typeof tla2tools.runTlc;
        };

        const originalGetSpecFiles = checkModelMutable.getSpecFiles;
        const originalMapLine = checkModelMutable.mapTlcOutputLine;
        const originalBindTo = checkModelMutable.outChannel.bindTo;
        const originalExists = commonMutable.exists;
        const originalRunTlc = tla2toolsMutable.runTlc;
        let runTlcCalls = 0;

        const specFiles = new SpecFiles(
            path.join(__dirname, 'Example.tla'),
            path.join(__dirname, 'MCExample.cfg')
        );

        checkModelMutable.getSpecFiles = async () => specFiles;
        checkModelMutable.mapTlcOutputLine = (line: string) => line.trim();
        checkModelMutable.outChannel.bindTo = () => { /* no-op */ };
        commonMutable.exists = async () => true;

        const mockProcess = new MockProcess();
        tla2toolsMutable.runTlc = async () => {
            runTlcCalls++;
            return new ToolProcessInfo('tlc', mockProcess as unknown as ChildProcess);
        };

        try {
            const tool = new CheckModuleTool();
            const cts = new vscode.CancellationTokenSource();

            const filePath = path.join(__dirname, 'Example.tla');
            const options = {
                toolInvocationToken: undefined,
                input: {
                    fileName: filePath
                }
            } as unknown as LanguageModelToolInvocationOptions<FileParameter>;

            const invokePromise = tool.invoke(options, cts.token);

            // Wait until TLC process has been started before triggering cancellation.
            while (runTlcCalls === 0) {
                await new Promise(resolve => setTimeout(resolve, 0));
            }

            cts.cancel();
            mockProcess.emit('close', 130);
            const result = await invokePromise;

            assert.strictEqual(mockProcess.killed, true, 'Cancellation should kill the TLC process');
            assert.strictEqual(result.content.length, 1);
            const [part] = result.content;
            assert.ok(part instanceof vscode.LanguageModelTextPart, 'Result should be a text part');
            assert.strictEqual((part as vscode.LanguageModelTextPart).value,
                `Model checking cancelled for ${filePath}.`);
        } finally {
            checkModelMutable.getSpecFiles = originalGetSpecFiles;
            checkModelMutable.mapTlcOutputLine = originalMapLine;
            checkModelMutable.outChannel.bindTo = originalBindTo;
            commonMutable.exists = originalExists;
            tla2toolsMutable.runTlc = originalRunTlc;
        }
    });
});

suite('TLC Tool explicit configFileName', () => {
    let tmpDir: string;

    setup(async () => {
        tmpDir = await fsp.mkdtemp(path.join(os.tmpdir(), 'tlc-tool-cfg-test-'));
    });

    teardown(async () => {
        await fsp.rm(tmpDir, { recursive: true, force: true });
    });

    async function writeFiles(...names: string[]): Promise<void> {
        for (const name of names) {
            await fsp.writeFile(path.join(tmpDir, name), '');
        }
    }

    async function captureRunTlcArgs(input: FileParameter): Promise<string[][]> {
        const outChannel = checkModel.outChannel;
        const tla2toolsMutable = tla2tools as unknown as {
            runTlc: typeof tla2tools.runTlc;
        };
        const originalBindTo = outChannel.bindTo;
        const originalRunTlc = tla2toolsMutable.runTlc;
        const calls: string[][] = [];

        outChannel.bindTo = () => { /* no-op */ };
        tla2toolsMutable.runTlc = async (tlaFilePath: string, cfgFilePath: string) => {
            calls.push([tlaFilePath, cfgFilePath]);
            const mockProcess = new MockProcess();
            setTimeout(() => mockProcess.emit('close', 0), 0);
            return new ToolProcessInfo('tlc', mockProcess as unknown as ChildProcess);
        };

        try {
            const options = {
                toolInvocationToken: undefined,
                input
            } as unknown as LanguageModelToolInvocationOptions<FileParameter>;
            await new CheckModuleTool().invoke(options, new vscode.CancellationTokenSource().token);
            return calls;
        } finally {
            outChannel.bindTo = originalBindTo;
            tla2toolsMutable.runTlc = originalRunTlc;
        }
    }

    test('runs TLC with the explicit config when no default config exists', async () => {
        await writeFiles('Spec.tla', 'Spec_other.cfg');
        const tlaFile = path.join(tmpDir, 'Spec.tla');
        const cfgFile = path.join(tmpDir, 'Spec_other.cfg');

        const calls = await captureRunTlcArgs({ fileName: tlaFile, configFileName: cfgFile });

        assert.deepStrictEqual(calls, [[tlaFile, cfgFile]]);
    });

    test('pairs the explicit config with the given module, not a discovered MC model', async () => {
        await writeFiles('Spec.tla', 'MCSpec.tla', 'MCSpec.cfg', 'Spec_other.cfg');
        const tlaFile = path.join(tmpDir, 'Spec.tla');
        const cfgFile = path.join(tmpDir, 'Spec_other.cfg');

        const calls = await captureRunTlcArgs({ fileName: tlaFile, configFileName: cfgFile });

        assert.deepStrictEqual(calls, [[tlaFile, cfgFile]]);
    });
});
