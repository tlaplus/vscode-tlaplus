import * as assert from 'assert';
import * as vscode from 'vscode';
import { TlapsClient } from '../../src/tlaps';

interface DecorationTypeSpy extends vscode.TextEditorDecorationType {
    disposed: boolean;
}

type ConfigListener = (event: vscode.ConfigurationChangeEvent) => void;

suite('TLAPS Client Test Suite', () => {
    const settings: { [key: string]: unknown } = {};
    const created: DecorationTypeSpy[] = [];
    const subscriptions: vscode.Disposable[] = [];
    let configListener: ConfigListener | undefined;
    let originalCreateDecorationType: typeof vscode.window.createTextEditorDecorationType;
    let originalGetConfiguration: typeof vscode.workspace.getConfiguration;
    let originalOnDidChangeConfiguration: typeof vscode.workspace.onDidChangeConfiguration;
    let originalRegisterTextEditorCommand: typeof vscode.commands.registerTextEditorCommand;

    setup(() => {
        settings['tlaplus.tlaps.enabled'] = false;
        settings['tlaplus.tlaps.lspServerCommand'] = [];
        settings['tlaplus.tlaps.wholeLine'] = true;
        created.length = 0;
        configListener = undefined;

        originalCreateDecorationType = vscode.window.createTextEditorDecorationType;
        (vscode.window as unknown as {
            createTextEditorDecorationType: () => vscode.TextEditorDecorationType
        }).createTextEditorDecorationType = () => {
            const decType: DecorationTypeSpy = {
                key: `tlaps-test-${created.length}`,
                disposed: false,
                dispose: () => {
                    decType.disposed = true;
                },
            };
            created.push(decType);
            return decType;
        };

        originalGetConfiguration = vscode.workspace.getConfiguration;
        (vscode.workspace as unknown as {
            getConfiguration: () => vscode.WorkspaceConfiguration
        }).getConfiguration = () => ({
            get: (key: string) => settings[key],
        } as unknown as vscode.WorkspaceConfiguration);

        originalOnDidChangeConfiguration = vscode.workspace.onDidChangeConfiguration;
        (vscode.workspace as unknown as {
            onDidChangeConfiguration: (listener: ConfigListener) => vscode.Disposable
        }).onDidChangeConfiguration = (listener: ConfigListener) => {
            configListener = listener;
            return new vscode.Disposable(() => undefined);
        };

        // The activated extension already owns the TLAPS commands.
        originalRegisterTextEditorCommand = vscode.commands.registerTextEditorCommand;
        (vscode.commands as unknown as {
            registerTextEditorCommand: () => vscode.Disposable
        }).registerTextEditorCommand = () => new vscode.Disposable(() => undefined);
    });

    teardown(() => {
        (vscode.window as unknown as {
            createTextEditorDecorationType: typeof vscode.window.createTextEditorDecorationType
        }).createTextEditorDecorationType = originalCreateDecorationType;
        (vscode.workspace as unknown as {
            getConfiguration: typeof vscode.workspace.getConfiguration
        }).getConfiguration = originalGetConfiguration;
        (vscode.workspace as unknown as {
            onDidChangeConfiguration: typeof vscode.workspace.onDidChangeConfiguration
        }).onDidChangeConfiguration = originalOnDidChangeConfiguration;
        (vscode.commands as unknown as {
            registerTextEditorCommand: typeof vscode.commands.registerTextEditorCommand
        }).registerTextEditorCommand = originalRegisterTextEditorCommand;
        subscriptions.splice(0).forEach(d => d.dispose());
    });

    test('Disposes the previous decoration types when the configuration changes', () => {
        const context = {
            subscriptions,
            asAbsolutePath: (relativePath: string) => relativePath,
        } as unknown as vscode.ExtensionContext;
        new TlapsClient(context, {} as vscode.DiagnosticCollection, () => undefined, () => undefined);
        const before = created.slice();
        assert.ok(before.length > 0, 'Expected decoration types on construction');
        assert.ok(configListener, 'Expected a configuration change listener');

        settings['tlaplus.tlaps.wholeLine'] = false;
        configListener({ affectsConfiguration: () => true });

        const after = created.slice(before.length);
        assert.strictEqual(after.length, before.length, 'Expected the decoration types to be recreated');
        assert.deepStrictEqual(
            before.filter(decType => !decType.disposed).map(decType => decType.key),
            [],
            'Decoration types from before the change must be disposed'
        );
        assert.deepStrictEqual(
            after.filter(decType => decType.disposed).map(decType => decType.key),
            [],
            'Current decoration types must stay registered'
        );
    });
});
