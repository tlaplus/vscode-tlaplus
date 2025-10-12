import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { EventEmitter } from 'events';
import { ChildProcess } from 'child_process';
import { PassThrough } from 'stream';
import { SpecFiles } from '../../../src/model/check';
import * as checkModel from '../../../src/commands/checkModel';
import * as tla2tools from '../../../src/tla2tools';
import { ValidationSnapshot } from '../../../src/model/specValidation';
import { ToolProcessInfo } from '../../../src/tla2tools';
import { DCollection } from '../../../src/diagnostic';
import * as tlcParserModule from '../../../src/parsers/tlc';

suite('Check Model Snapshot Integration', () => {
    test('doCheckModel uses snapshot paths and disposes on cancellation', async () => {
        const checkModelMutable = checkModel as unknown as {
            outChannel: typeof checkModel.outChannel;
        };
        const tla2toolsMutable = tla2tools as unknown as {
            runTlc: typeof tla2tools.runTlc;
        };

        const originalBindTo = checkModelMutable.outChannel.bindTo;
        const originalRunTlc = tla2toolsMutable.runTlc;

        const capturedArgs: unknown[][] = [];
        let disposeCalls = 0;

        checkModelMutable.outChannel.bindTo = () => { /* no-op */ };
        tla2toolsMutable.runTlc = async (...args) => {
            capturedArgs.push(args);
            return undefined;
        };

        const snapshot: ValidationSnapshot = {
            modelPath: path.join(__dirname, 'snapshot', 'MCSpec.tla'),
            configPath: path.join(__dirname, 'snapshot', 'MCSpec.cfg'),
            libraryPaths: [path.join(__dirname, 'snapshot')],
            resolveSnapshotToOriginal: () => path.join(__dirname, 'MCSpec.tla'),
            dispose: async () => { disposeCalls++; }
        };

        const specFiles = new SpecFiles(
            path.join(__dirname, 'MCSpec.tla'),
            path.join(__dirname, 'MCSpec.cfg')
        );
        const diagnostic = vscode.languages.createDiagnosticCollection('snapshot-test-cancel');

        try {
            const result = await checkModel.doCheckModel(
                specFiles,
                false,
                {} as vscode.ExtensionContext,
                diagnostic,
                false,
                [],
                undefined,
                snapshot
            );
            assert.strictEqual(result, undefined);
            assert.strictEqual(capturedArgs.length, 1);
            const args = capturedArgs[0];
            assert.strictEqual(args[0], snapshot.modelPath);
            assert.strictEqual(args[1], snapshot.configPath);
            assert.deepStrictEqual(args[5], snapshot.libraryPaths);
            assert.strictEqual(disposeCalls, 1, 'Snapshot should be disposed when TLC is not started');
        } finally {
            diagnostic.dispose();
            checkModelMutable.outChannel.bindTo = originalBindTo;
            tla2toolsMutable.runTlc = originalRunTlc;
        }
    });

    test('doCheckModel disposes snapshot after TLC process finishes', async () => {
        const checkModelMutable = checkModel as unknown as {
            outChannel: typeof checkModel.outChannel;
        };
        const tla2toolsMutable = tla2tools as unknown as {
            runTlc: typeof tla2tools.runTlc;
        };
        const tlcParserMutable = tlcParserModule as unknown as {
            TlcModelCheckerStdoutParser: typeof tlcParserModule.TlcModelCheckerStdoutParser;
        };

        const originalBindTo = checkModelMutable.outChannel.bindTo;
        const originalRunTlc = tla2toolsMutable.runTlc;
        const OriginalParser = tlcParserMutable.TlcModelCheckerStdoutParser;

        const parserArgs: unknown[][] = [];
        class StubParser {
            constructor(...args: unknown[]) {
                parserArgs.push(args);
            }
            async readAll(): Promise<DCollection> {
                return new DCollection();
            }
        }

        checkModelMutable.outChannel.bindTo = () => { /* no-op */ };
        tlcParserMutable.TlcModelCheckerStdoutParser = StubParser as unknown as typeof OriginalParser;

        const processEmitter = new EventEmitter() as unknown as ChildProcess;
        const stdout = new PassThrough();
        const stderr = new PassThrough();
        (processEmitter as unknown as { stdout: PassThrough }).stdout = stdout;
        (processEmitter as unknown as { stderr: PassThrough }).stderr = stderr;
        (processEmitter as { kill: () => void }).kill = () => { /* no-op */ };

        let disposeCalls = 0;
        const snapshot: ValidationSnapshot = {
            modelPath: path.join(__dirname, 'snapshot', 'RunMCSpec.tla'),
            configPath: path.join(__dirname, 'snapshot', 'RunMCSpec.cfg'),
            libraryPaths: [path.join(__dirname, 'snapshot')],
            resolveSnapshotToOriginal: () => path.join(__dirname, 'RunMCSpec.tla'),
            dispose: async () => { disposeCalls++; }
        };

        let runTlcArgs: unknown[] | undefined;
        tla2toolsMutable.runTlc = async (...args) => {
            runTlcArgs = args;
            return new ToolProcessInfo('tlc', processEmitter);
        };

        const specFiles = new SpecFiles(
            path.join(__dirname, 'RunMCSpec.tla'),
            path.join(__dirname, 'RunMCSpec.cfg')
        );
        const diagnostic = vscode.languages.createDiagnosticCollection('snapshot-test-run');

        try {
            const runPromise = checkModel.doCheckModel(
                specFiles,
                false,
                {} as vscode.ExtensionContext,
                diagnostic,
                false,
                [],
                undefined,
                snapshot
            );

            const result = await runPromise;
            assert.strictEqual(result, undefined);
            assert.ok(runTlcArgs, 'runTlc should be invoked');
            assert.strictEqual(runTlcArgs![0], snapshot.modelPath);
            assert.strictEqual(runTlcArgs![1], snapshot.configPath);
            assert.deepStrictEqual(runTlcArgs![5], snapshot.libraryPaths);
            assert.strictEqual(disposeCalls, 0, 'Snapshot should not dispose before TLC finishes');
            assert.ok(parserArgs.length > 0, 'Stdout parser should be instantiated');

            (processEmitter as EventEmitter).emit('close', 0);
            await new Promise((resolve) => setImmediate(resolve));
            assert.strictEqual(disposeCalls, 1, 'Snapshot should dispose after TLC closes');
        } finally {
            diagnostic.dispose();
            checkModelMutable.outChannel.bindTo = originalBindTo;
            tla2toolsMutable.runTlc = originalRunTlc;
            tlcParserMutable.TlcModelCheckerStdoutParser = OriginalParser;
            stdout.destroy();
            stderr.destroy();
        }
    });
});
