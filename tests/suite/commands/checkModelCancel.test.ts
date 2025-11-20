import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';

suite('CheckModel cancellation handling', () => {
    const tla2toolsPath = require.resolve(path.resolve(__dirname, '../../../src/tla2tools'));
    const checkModelPath = require.resolve(path.resolve(__dirname, '../../../src/commands/checkModel'));
    const modelPath = require.resolve(path.resolve(__dirname, '../../../src/model/check'));

    let originalTla2tools: typeof import('../../../src/tla2tools') | undefined;
    let originalExecuteCommand: typeof vscode.commands.executeCommand | undefined;

    const makeCacheEntry = (exports: unknown): NodeJS.Module => ({
        id: tla2toolsPath,
        filename: tla2toolsPath,
        loaded: true,
        exports,
        parent: null,
        path: tla2toolsPath,
        paths: [],
        children: [],
        require,
        isPreloading: false,
    } as unknown as NodeJS.Module);

    setup(() => {
        // Ensure a clean slate for module cache
        delete require.cache[checkModelPath];
        delete require.cache[tla2toolsPath];
    });

    teardown(() => {
        // Restore executeCommand and cached modules
        if (originalExecuteCommand) {
            (vscode.commands as unknown as { executeCommand: typeof vscode.commands.executeCommand })
                .executeCommand = originalExecuteCommand;
        }
        if (originalTla2tools) {
            require.cache[tla2toolsPath] = makeCacheEntry(originalTla2tools);
        } else {
            delete require.cache[tla2toolsPath];
        }
        delete require.cache[checkModelPath];
    });

    test('does not leave TLC running context when launch is cancelled', async function() {
        this.timeout(5000);
        originalTla2tools = await import(tla2toolsPath);

        // Stub runTlc to simulate user cancelling the options prompt
        const stubbedTla2tools = {
            ...originalTla2tools,
            runTlc: async () => undefined,
        } as typeof import('../../../src/tla2tools');
        require.cache[tla2toolsPath] = makeCacheEntry(stubbedTla2tools);

        // Capture context updates
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

        const specFiles = new SpecFiles('Dummy.tla', 'Dummy.cfg');
        const diagnostics = vscode.languages.createDiagnosticCollection('cancel-test');

        await doCheckModel(specFiles, true, {} as vscode.ExtensionContext, diagnostics, true);

        diagnostics.dispose();

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
});
