import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import {
    CMD_MODEL_EDITOR_DISPLAY
} from '../../../src/panels/modelEditorView';

const CFG_KEY = 'tlaplus.modelEditor.enabled';
const FIXTURE_TLA = path.resolve(
    __dirname, '..', '..', 'fixtures', 'DivergenceTest.tla'
);

async function setEnabled(value: boolean | undefined): Promise<void> {
    await vscode.workspace.getConfiguration().update(
        CFG_KEY, value, vscode.ConfigurationTarget.Global
    );
}

function modelEditorTabs(): vscode.Tab[] {
    return vscode.window.tabGroups.all
        .flatMap((g) => g.tabs)
        .filter((t) => t.label.startsWith('TLA+ Model Editor'));
}

async function closeModelEditorTabs(): Promise<void> {
    const tabs = modelEditorTabs();
    if (tabs.length > 0) {
        await vscode.window.tabGroups.close(tabs);
    }
}

suite('Model Editor View Test Suite', () => {

    suiteTeardown(async () => {
        await closeModelEditorTabs();
        await setEnabled(undefined);
    });

    test('Command is registered', async () => {
        const commands = await vscode.commands.getCommands(true);
        assert.ok(
            commands.includes(CMD_MODEL_EDITOR_DISPLAY),
            `Expected command ${CMD_MODEL_EDITOR_DISPLAY} to be registered`
        );
    });

    test('Setting enabled: invoking the command opens the model editor', async () => {
        await setEnabled(true);
        await closeModelEditorTabs();

        await vscode.commands.executeCommand(
            CMD_MODEL_EDITOR_DISPLAY, vscode.Uri.file(FIXTURE_TLA)
        );
        // Poll for the tab to appear (up to 2s)
        let tabs = modelEditorTabs();
        const deadline = Date.now() + 2000;
        while (tabs.length === 0 && Date.now() < deadline) {
            await new Promise((r) => setTimeout(r, 50));
            tabs = modelEditorTabs();
        }
        assert.strictEqual(
            tabs.length, 1,
            'Exactly one model editor tab should be open when enabled'
        );
    });
});
