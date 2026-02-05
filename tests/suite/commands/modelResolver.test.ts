import * as assert from 'assert';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { resolveModelForUri } from '../../../src/commands/modelResolver';

suite('Model Resolver', () => {
    let testDir: string;
    let originalShowWarning: typeof vscode.window.showWarningMessage;
    let originalShowQuickPick: typeof vscode.window.showQuickPick;

    setup(() => {
        testDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-model-resolver-'));
        originalShowWarning = vscode.window.showWarningMessage;
        originalShowQuickPick = vscode.window.showQuickPick;
    });

    teardown(() => {
        (vscode.window as unknown as { showWarningMessage: typeof vscode.window.showWarningMessage })
            .showWarningMessage = originalShowWarning;
        (vscode.window as unknown as { showQuickPick: typeof vscode.window.showQuickPick })
            .showQuickPick = originalShowQuickPick;

        if (fs.existsSync(testDir)) {
            fs.rmSync(testDir, { recursive: true, force: true });
        }
    });

    test('Resolves adjacent Spec.cfg', async () => {
        const tlaPath = path.join(testDir, 'Spec.tla');
        const cfgPath = path.join(testDir, 'Spec.cfg');
        fs.writeFileSync(tlaPath, '---- MODULE Spec ----\n====');
        fs.writeFileSync(cfgPath, 'INIT Init');

        const result = await resolveModelForUri(vscode.Uri.file(tlaPath), true, false);
        assert.ok(result, 'Expected resolved model');
        assert.strictEqual(result?.tlaPath, vscode.Uri.file(tlaPath).fsPath);
        assert.strictEqual(result?.cfgPath, vscode.Uri.file(cfgPath).fsPath);
        assert.strictEqual(result?.modelName, 'Spec');
    });

    test('Resolves MC-prefixed model when only MC files exist', async () => {
        const tlaPath = path.join(testDir, 'Spec.tla');
        const mcTlaPath = path.join(testDir, 'MCSpec.tla');
        const mcCfgPath = path.join(testDir, 'MCSpec.cfg');
        fs.writeFileSync(tlaPath, '---- MODULE Spec ----\n====');
        fs.writeFileSync(mcTlaPath, '---- MODULE MCSpec ----\n====');
        fs.writeFileSync(mcCfgPath, 'INIT Init');

        const result = await resolveModelForUri(vscode.Uri.file(tlaPath), true, false);
        assert.ok(result, 'Expected resolved model');
        assert.strictEqual(result?.tlaPath, vscode.Uri.file(mcTlaPath).fsPath);
        assert.strictEqual(result?.cfgPath, vscode.Uri.file(mcCfgPath).fsPath);
        assert.strictEqual(result?.modelName, 'MCSpec');
    });

    test('Interactive selection chooses the picked model when multiple exist', async () => {
        const tlaPath = path.join(testDir, 'Spec.tla');
        const cfgPath = path.join(testDir, 'Spec.cfg');
        const mcTlaPath = path.join(testDir, 'MCSpec.tla');
        const mcCfgPath = path.join(testDir, 'MCSpec.cfg');
        fs.writeFileSync(tlaPath, '---- MODULE Spec ----\n====');
        fs.writeFileSync(cfgPath, 'INIT Init');
        fs.writeFileSync(mcTlaPath, '---- MODULE MCSpec ----\n====');
        fs.writeFileSync(mcCfgPath, 'INIT Init');

        const quickPick = async (items: readonly unknown[]) => items[1];
        (vscode.window as unknown as { showQuickPick: typeof vscode.window.showQuickPick }).showQuickPick =
            quickPick as unknown as typeof vscode.window.showQuickPick;

        const result = await resolveModelForUri(vscode.Uri.file(tlaPath), true, true);
        assert.ok(result, 'Expected resolved model');
        assert.strictEqual(result?.cfgPath, vscode.Uri.file(mcCfgPath).fsPath);
    });

    test('Non-interactive selection prefers Spec.cfg when multiple exist', async () => {
        const tlaPath = path.join(testDir, 'Spec.tla');
        const cfgPath = path.join(testDir, 'Spec.cfg');
        const mcTlaPath = path.join(testDir, 'MCSpec.tla');
        const mcCfgPath = path.join(testDir, 'MCSpec.cfg');
        fs.writeFileSync(tlaPath, '---- MODULE Spec ----\n====');
        fs.writeFileSync(cfgPath, 'INIT Init');
        fs.writeFileSync(mcTlaPath, '---- MODULE MCSpec ----\n====');
        fs.writeFileSync(mcCfgPath, 'INIT Init');

        const result = await resolveModelForUri(vscode.Uri.file(tlaPath), true, false);
        assert.ok(result, 'Expected resolved model');
        assert.strictEqual(result?.cfgPath, vscode.Uri.file(cfgPath).fsPath);
    });

    test('Returns undefined when cfg has no matching tla', async () => {
        const cfgPath = path.join(testDir, 'Spec.cfg');
        fs.writeFileSync(cfgPath, 'INIT Init');

        let warningShown = false;
        (vscode.window as unknown as { showWarningMessage: typeof vscode.window.showWarningMessage }).showWarningMessage =
            async () => {
                warningShown = true;
                return undefined;
            };

        const result = await resolveModelForUri(vscode.Uri.file(cfgPath), true, true);
        assert.strictEqual(result, undefined);
        assert.strictEqual(warningShown, true, 'Expected warning message to be shown');
    });

    test('Custom pick allows selecting .tla as config and strips extension', async () => {
        const tlaPath = path.join(testDir, 'Spec.tla');
        const altTlaPath = path.join(testDir, 'Alt.tla');
        fs.writeFileSync(tlaPath, '---- MODULE Spec ----\n====');
        fs.writeFileSync(altTlaPath, '---- MODULE Alt ----\n====');

        const quickPick = async (items: readonly unknown[]) => items.find((item) => item === 'Alt.tla');
        (vscode.window as unknown as { showQuickPick: typeof vscode.window.showQuickPick }).showQuickPick =
            quickPick as unknown as typeof vscode.window.showQuickPick;

        const result = await resolveModelForUri(vscode.Uri.file(tlaPath), true, true, 'customPick');
        assert.ok(result, 'Expected resolved model');
        assert.strictEqual(result?.tlaPath, vscode.Uri.file(tlaPath).fsPath);
        assert.strictEqual(result?.cfgPath, vscode.Uri.file(altTlaPath).fsPath);
        assert.strictEqual(result?.modelName, 'Alt');
        assert.strictEqual(result?.outputDir, vscode.Uri.file(testDir).fsPath);
    });
});
