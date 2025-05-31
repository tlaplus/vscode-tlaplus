import * as assert from 'assert';
import * as vscode from 'vscode';
import { revealEmptyCheckResultView, isCheckResultViewPanelFocused } from '../../../src/panels/checkResultView';

suite('Check Result View Test Suite', () => {
    let doc: vscode.TextDocument;
    const configKey = 'tlaplus.tlc.modelChecker.preserveEditorFocus';

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({
            content: 'test content',
            language: 'tlaplus'
        });
        await vscode.window.showTextDocument(doc);
    });

    async function setPreserveEditorFocus(value: boolean) {
        await vscode.workspace.getConfiguration().update(
            configKey,
            value,
            vscode.ConfigurationTarget.Global
        );
    }

    suiteTeardown(async () => {
        await vscode.workspace.getConfiguration().update(
            configKey,
            undefined,
            vscode.ConfigurationTarget.Global
        );
        await vscode.window.showTextDocument(doc, {preview: true, preserveFocus: false});
        return vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Preserves editor focus when configured', async () => {
        await setPreserveEditorFocus(true);

        revealEmptyCheckResultView({
            extensionUri: vscode.Uri.file(__dirname)
        } as vscode.ExtensionContext);

        // Wait a bit to ensure any potential focus changes would have happened
        await new Promise(resolve => setTimeout(resolve, 300));

        // Verify the editor is still focused
        assert.ok(!isCheckResultViewPanelFocused(), 'Expected editor to remain focused');
    });

    test('Switches focus to panel when preserveEditorFocus is disabled', async function() {
        await setPreserveEditorFocus(false);

        revealEmptyCheckResultView({
            extensionUri: vscode.Uri.file(__dirname)
        } as vscode.ExtensionContext);

        // Wait a bit to ensure any potential focus changes would have happened
        await new Promise(resolve => setTimeout(resolve, 300));

        assert.ok(isCheckResultViewPanelFocused(),
            'Expected editor to lose focus when preserveEditorFocus is disabled');
    });
});