import * as assert from 'assert';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { SanyData } from '../../../src/parsers/sany';

suite('CheckModel cancellation handling', () => {
    const fsp = fs.promises;
    const tla2toolsPath = require.resolve(path.resolve(__dirname, '../../../src/tla2tools'));
    const parseModulePath = require.resolve(path.resolve(__dirname, '../../../src/commands/parseModule'));
    const checkModelPath = require.resolve(path.resolve(__dirname, '../../../src/commands/checkModel'));
    const modelPath = require.resolve(path.resolve(__dirname, '../../../src/model/check'));
    const checkResultViewPath = require.resolve(path.resolve(__dirname, '../../../src/panels/checkResultView'));

    let originalTla2tools: typeof import('../../../src/tla2tools') | undefined;
    let originalParseModule: typeof import('../../../src/commands/parseModule') | undefined;
    let originalCheckResultView: typeof import('../../../src/panels/checkResultView') | undefined;
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
});
