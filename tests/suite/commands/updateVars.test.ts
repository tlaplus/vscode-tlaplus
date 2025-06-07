import * as vscode from 'vscode';
import * as assert from 'assert';
import { beforeEach, afterEach } from 'mocha';
import { replaceDocContents } from '../document';

suite('Update vars Command Test Suite', () => {
    let doc: vscode.TextDocument;

    beforeEach(async () => {
        doc = await vscode.workspace.openTextDocument({
            language: 'tlaplus',
            content: ''
        });
        await vscode.window.showTextDocument(doc);
    });

    afterEach(async () => {
        await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    // Helper to join lines with the document's EOL sequence
    function joinLines(lines: string[]): string {
        const eol = doc.eol === vscode.EndOfLine.CRLF ? '\r\n' : '\n';
        return lines.join(eol);
    }

    test('Updates simple single-line vars', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLES x, y, z',
            'vars == <<x, y>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLES x, y, z',
            'vars == <<x, y, z>>'
        ]));
    });

    test('Handles no variables in document', async () => {
        await replaceDocContents(doc, 'vars == <<>>');

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        // Should show info message and not change document
        assert.strictEqual(doc.getText(), 'vars == <<>>');
    });

    test('Handles no vars definition', async () => {
        await replaceDocContents(doc, 'VARIABLES x, y, z');

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        // Should show info message and not change document
        assert.strictEqual(doc.getText(), 'VARIABLES x, y, z');
    });

    test('Preserves order of variable declarations', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLES z, x, y',
            'vars == <<>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLES z, x, y',
            'vars == <<z, x, y>>'
        ]));
    });

    test('Handles multiple VARIABLES declarations', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLES x, y',
            'VARIABLES z',
            'vars == <<x>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLES x, y',
            'VARIABLES z',
            'vars == <<x, y, z>>'
        ]));
    });

    test('Does not update when vars is already correct', async () => {
        const originalContent = joinLines([
            'VARIABLES x, y, z',
            'vars == <<x, y, z>>'
        ]);

        await replaceDocContents(doc, originalContent);

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        // Should not change when already up to date
        assert.strictEqual(doc.getText(), originalContent);
    });

    test('Handles removing variables', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLES x, z',
            'vars == <<x, y, z>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLES x, z',
            'vars == <<x, z>>'
        ]));
    });

    test('Handles VARIABLE (singular) keyword', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLE x',
            'VARIABLES y, z',
            'vars == <<>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLE x',
            'VARIABLES y, z',
            'vars == <<x, y, z>>'
        ]));
    });

    test('Converts long single-line vars to multi-line', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLES a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p',
            'vars == <<>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLES a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p',
            'vars == <<',
            '    a, b, c, d,',
            '    e, f, g, h,',
            '    i, j, k, l,',
            '    m, n, o, p',
            '>>'
        ]));
    });

    test('Preserves multi-line format with 2 items per line', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLES x, y, z, w',
            'vars == <<',
            '    x, y',
            '>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        // Should maintain 2 items per line pattern
        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLES x, y, z, w',
            'vars == <<',
            '    x, y,',
            '    z, w',
            '>>'
        ]));
    });

    test('Handles multi-line vars with different items per line', async () => {
        await replaceDocContents(doc, joinLines([
            'VARIABLES a, b, c, d, e, f',
            'vars == <<',
            '    a, b, c,',
            '    d',
            '>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            'VARIABLES a, b, c, d, e, f',
            'vars == <<',
            '    a, b, c,',
            '    d, e, f',
            '>>'
        ]));
    });

    test('Detects PlusCal algorithm and includes pc/stack by default', async () => {
        await replaceDocContents(doc, joinLines([
            '(*--algorithm test',
            'variables x = 0, y = 0;',
            'begin',
            '  skip;',
            'end algorithm; *)',
            '',
            'VARIABLES x, y, pc, stack',
            'vars == <<x, y>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            '(*--algorithm test',
            'variables x = 0, y = 0;',
            'begin',
            '  skip;',
            'end algorithm; *)',
            '',
            'VARIABLES x, y, pc, stack',
            'vars == <<x, y, pc, stack>>'
        ]));
    });

    test('Excludes PlusCal variables when configured', async () => {
        // Save original config
        const config = vscode.workspace.getConfiguration('tlaplus.refactor');
        const originalValue = config.get<boolean>('includePlusCalVariables');

        try {
            // Set config to exclude PlusCal vars
            await config.update('includePlusCalVariables', false, vscode.ConfigurationTarget.Global);

            await replaceDocContents(doc, joinLines([
                '(*--algorithm test',
                'variables x = 0, y = 0;',
                'begin',
                '  skip;',
                'end algorithm; *)',
                '',
                'VARIABLES x, y, pc, stack',
                'vars == <<x, y, pc, stack>>'
            ]));

            await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

            assert.strictEqual(doc.getText(), joinLines([
                '(*--algorithm test',
                'variables x = 0, y = 0;',
                'begin',
                '  skip;',
                'end algorithm; *)',
                '',
                'VARIABLES x, y, pc, stack',
                'vars == <<x, y>>'
            ]));
        } finally {
            // Restore original config
            await config.update('includePlusCalVariables', originalValue, vscode.ConfigurationTarget.Global);
        }
    });

    test('Handles PlusCal with --fair algorithm', async () => {
        await replaceDocContents(doc, joinLines([
            '(*--fair algorithm fairtest',
            'variables z = 0;',
            'begin',
            '  skip;',
            'end algorithm; *)',
            '',
            'VARIABLES z, pc',
            'vars == <<z>>'
        ]));

        await vscode.commands.executeCommand('tlaplus.refactor.update_vars');

        assert.strictEqual(doc.getText(), joinLines([
            '(*--fair algorithm fairtest',
            'variables z = 0;',
            'begin',
            '  skip;',
            'end algorithm; *)',
            '',
            'VARIABLES z, pc',
            'vars == <<z, pc>>'
        ]));
    });
});