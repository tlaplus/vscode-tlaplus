import * as vscode from 'vscode';
import * as assert from 'assert';
import { beforeEach, afterEach } from 'mocha';
import { replaceDocContents } from '../document';
import { TlaCodeActionProvider } from '../../../src/actions';

suite('TLA+ Code Actions Test Suite', () => {
    let doc: vscode.TextDocument;
    let provider: TlaCodeActionProvider;

    beforeEach(async () => {
        doc = await vscode.workspace.openTextDocument({
            language: 'tlaplus',
            content: ''
        });
        await vscode.window.showTextDocument(doc);
        provider = new TlaCodeActionProvider();
    });

    afterEach(async () => {
        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Provides Update vars tuple action on vars line', async () => {
        await replaceDocContents(doc, [
            'VARIABLES x, y, z',
            'vars == <<x, y>>'
        ].join('\n'));

        // Get code actions for line 1 (vars line)
        const position = new vscode.Position(1, 0);
        const range = new vscode.Range(position, position);
        const context: vscode.CodeActionContext = {
            diagnostics: [],
            only: undefined,
            triggerKind: vscode.CodeActionTriggerKind.Invoke
        };

        const actions = await provider.provideCodeActions(
            doc,
            range,
            context,
            new vscode.CancellationTokenSource().token
        );

        assert.ok(actions, 'Should provide actions');
        assert.ok(Array.isArray(actions), 'Actions should be an array');

        const updateVarsAction = actions.find(action =>
            'title' in action && action.title === 'Update vars tuple'
        ) as vscode.CodeAction | undefined;

        assert.ok(updateVarsAction, 'Should provide Update vars tuple action');
        assert.ok(updateVarsAction?.kind?.contains(vscode.CodeActionKind.RefactorRewrite),
            'Should be a refactor action');
    });

    test('Does not provide Update vars action on non-vars line', async () => {
        await replaceDocContents(doc, [
            'VARIABLES x, y, z',
            'vars == <<x, y>>',
            'Init == x = 0'
        ].join('\n'));

        // Get code actions for line 2 (Init line)
        const position = new vscode.Position(2, 0);
        const range = new vscode.Range(position, position);
        const context: vscode.CodeActionContext = {
            diagnostics: [],
            only: undefined,
            triggerKind: vscode.CodeActionTriggerKind.Invoke
        };

        const actions = await provider.provideCodeActions(
            doc,
            range,
            context,
            new vscode.CancellationTokenSource().token
        );

        assert.ok(actions, 'Should provide actions');
        assert.ok(Array.isArray(actions), 'Actions should be an array');

        const updateVarsAction = actions.find(action =>
            'title' in action && action.title === 'Update vars tuple'
        );

        assert.ok(!updateVarsAction, 'Should not provide Update vars tuple action on non-vars line');
    });

    test('Update vars action triggers command', async () => {
        await replaceDocContents(doc, [
            'VARIABLES x, y, z',
            'vars == <<x, y>>'
        ].join('\n'));

        // Get code actions for line 1 (vars line)
        const position = new vscode.Position(1, 0);
        const range = new vscode.Range(position, position);
        const context: vscode.CodeActionContext = {
            diagnostics: [],
            only: undefined,
            triggerKind: vscode.CodeActionTriggerKind.Invoke
        };

        const actions = await provider.provideCodeActions(
            doc,
            range,
            context,
            new vscode.CancellationTokenSource().token
        );

        const updateVarsAction = actions?.find(action =>
            'title' in action && action.title === 'Update vars tuple'
        ) as vscode.CodeAction | undefined;

        assert.ok(updateVarsAction, 'Should find Update vars tuple action');
        assert.ok(updateVarsAction?.command, 'Action should have a command');
        assert.strictEqual(updateVarsAction?.command?.command, 'tlaplus.refactor.update_vars',
            'Should trigger the correct command');
    });
});