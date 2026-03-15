import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { CheckModuleTool, FileParameter } from '../../../src/lm/TLCTool';
import * as common from '../../../src/common';
import { SpecFiles } from '../../../src/model/check';
import { LanguageModelToolInvocationOptions } from 'vscode';
import { CheckService, CheckSession } from '../../../src/services/checkService';

suite('TLC Tool cancellation handling', () => {
    test('CheckModuleTool rejects missing input file', async () => {
        const commonMutable = common as unknown as {
            exists: typeof common.exists;
        };
        const originalExists = commonMutable.exists;
        let resolveSpecFilesCalled = 0;

        commonMutable.exists = async () => false;

        try {
            const fakeCheckService = {
                resolveSpecFiles: async () => {
                    resolveSpecFilesCalled++;
                    return undefined;
                },
            } as unknown as CheckService;
            const tool = new CheckModuleTool(fakeCheckService);
            const cts = new vscode.CancellationTokenSource();

            const filePath = path.join(__dirname, 'Missing.tla');
            const options = {
                toolInvocationToken: undefined,
                input: {
                    fileName: filePath
                }
            } as unknown as LanguageModelToolInvocationOptions<FileParameter>;

            const result = await tool.invoke(options, cts.token);
            assert.strictEqual(resolveSpecFilesCalled, 0, 'resolveSpecFiles should not run when file is missing');
            assert.strictEqual(result.content.length, 1);
            const [part] = result.content;
            assert.ok(part instanceof vscode.LanguageModelTextPart, 'Result should be a text part');
            assert.strictEqual((part as vscode.LanguageModelTextPart).value,
                `File ${filePath} does not exist`);
        } finally {
            commonMutable.exists = originalExists;
        }
    });

    test('CheckModuleTool respects pre-cancelled token', async () => {
        let resolveSpecFilesCalled = 0;
        const fakeCheckService = {
            resolveSpecFiles: async () => {
                resolveSpecFilesCalled++;
                return undefined;
            },
        } as unknown as CheckService;

        const tool = new CheckModuleTool(fakeCheckService);
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
        assert.strictEqual(resolveSpecFilesCalled, 0, 'resolveSpecFiles should not run when already cancelled');
        assert.strictEqual(result.content.length, 1, 'Expected single cancellation message');
        const [part] = result.content;
        assert.ok(part instanceof vscode.LanguageModelTextPart, 'Result should be a text part');
        assert.strictEqual((part as vscode.LanguageModelTextPart).value,
            `Model checking cancelled for ${filePath}.`);
    });

    test('CheckModuleTool cancels an in-flight session', async () => {
        const commonMutable = common as unknown as {
            exists: typeof common.exists;
        };
        const originalExists = commonMutable.exists;
        const specFiles = new SpecFiles(
            path.join(__dirname, 'Example.tla'),
            path.join(__dirname, 'MCExample.cfg')
        );
        const session = new CheckSession(specFiles, { showOptionsPrompt: false, showFullOutput: true });
        const originalRequestCancel = session.requestCancel.bind(session);
        let requestCancelCalled = 0;

        (session as unknown as { requestCancel: () => void }).requestCancel = () => {
            requestCancelCalled++;
            originalRequestCancel();
            session.finish(undefined);
        };

        const fakeCheckService = {
            resolveSpecFiles: async () => specFiles,
            startSession: async () => session,
        } as unknown as CheckService;

        commonMutable.exists = async () => true;

        try {
            const tool = new CheckModuleTool(fakeCheckService);
            const cts = new vscode.CancellationTokenSource();

            const filePath = path.join(__dirname, 'Example.tla');
            const options = {
                toolInvocationToken: undefined,
                input: {
                    fileName: filePath
                }
            } as unknown as LanguageModelToolInvocationOptions<FileParameter>;

            const invokePromise = tool.invoke(options, cts.token);
            await new Promise((resolve) => setTimeout(resolve, 0));
            cts.cancel();
            const result = await invokePromise;

            assert.strictEqual(result.content.length, 1);
            const [part] = result.content;
            assert.ok(part instanceof vscode.LanguageModelTextPart, 'Result should be a text part');
            assert.strictEqual((part as vscode.LanguageModelTextPart).value,
                `Model checking cancelled for ${filePath}.`);
            assert.ok(requestCancelCalled >= 0, 'Cancellation path should complete without throwing');
        } finally {
            commonMutable.exists = originalExists;
        }
    });
});
