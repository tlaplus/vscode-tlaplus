import * as assert from 'assert';
import * as vscode from 'vscode';
import { CheckResultViewController } from '../../../src/panels/checkResultView';

suite('Check Result View Test Suite', () => {
    let doc: vscode.TextDocument;
    let controller: CheckResultViewController;
    const configKey = 'tlaplus.tlc.modelChecker.preserveEditorFocus';

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({
            content: 'test content',
            language: 'tlaplus'
        });
        controller = new CheckResultViewController(vscode.Uri.file(__dirname));
        await vscode.window.showTextDocument(doc);
    });

    async function setPreserveEditorFocus(value: boolean) {
        await vscode.workspace.getConfiguration().update(
            configKey,
            value,
            vscode.ConfigurationTarget.Global
        );
    }

    async function waitForFocusState(expectedPanelFocused: boolean, timeoutMs = 2000): Promise<boolean> {
        const startTime = Date.now();
        while (Date.now() - startTime < timeoutMs) {
            if (controller.isFocused() === expectedPanelFocused) {
                return true;
            }
            await new Promise(resolve => setTimeout(resolve, 50));
        }
        return false;
    }

    suiteTeardown(async () => {
        await vscode.workspace.getConfiguration().update(
            configKey,
            undefined,
            vscode.ConfigurationTarget.Global
        );
        await vscode.window.showTextDocument(doc, {preview: true, preserveFocus: false});
        controller.dispose();
        return vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Preserves editor focus when configured', async () => {
        await setPreserveEditorFocus(true);

        controller.revealEmpty();

        const success = await waitForFocusState(false);
        assert.ok(success, 'Timed out waiting for editor to remain focused');
        assert.ok(!controller.isFocused(), 'Expected editor to remain focused');
    });

    test('Switches focus to panel when preserveEditorFocus is disabled', async function() {
        await setPreserveEditorFocus(false);

        controller.revealEmpty();

        const success = await waitForFocusState(true);
        assert.ok(success, 'Timed out waiting for panel to gain focus');
        assert.ok(controller.isFocused(),
            'Expected editor to lose focus when preserveEditorFocus is disabled');
    });
});
