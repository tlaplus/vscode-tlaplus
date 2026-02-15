import * as assert from 'assert';
import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import { extractModuleName } from '../../../src/formatters/tlaFormatter';
import { applyDocEdits, replaceDocContents } from '../document';

const UNFORMATTED =
    'This is some text explaining the spec.\n' +
    '---------------------- MODULE HourClock ----------------------\n' +
    'EXTENDS Naturals, TLC\n' +
    'VARIABLE hr\n' +
    'HCini  ==  hr \\in (1 .. 12)\n' +
    'HCnxt  ==  hr\' = IF hr # 12 THEN hr + 1 ELSE 1\n' +
    'HC  ==  HCini /\\ [][HCnxt]_hr\n' +
    '--------------------------------------------------------------\n' +
    'THEOREM  HC => []HCini\n' +
    '==============================================================\n' +
    'This is post text\n' +
    'Has multiple lines in it.\n';

const EXPECTED =
    'This is some text explaining the spec.\n' +
    '---------------------- MODULE HourClock ----------------------\n' +
    'EXTENDS Naturals, TLC\n' +
    'VARIABLE hr\n' +
    'HCini == hr \\in ( 1 .. 12 )\n' +
    'HCnxt == hr\' = IF hr # 12 THEN hr + 1 ELSE 1\n' +
    'HC == HCini /\\ [][HCnxt]_hr\n' +
    '--------------------------------------------------------------\n' +
    'THEOREM HC => []HCini\n' +
    '==============================================================\n' +
    'This is post text\n' +
    'Has multiple lines in it.\n';

async function formatDocument(doc: vscode.TextDocument): Promise<void> {
    const edits = await vscode.commands.executeCommand<vscode.TextEdit[]>(
        'vscode.executeFormatDocumentProvider',
        doc.uri,
        { insertSpaces: true, tabSize: 4 } as vscode.FormattingOptions
    );
    assert.ok(edits && edits.length > 0, `Expected formatting edits but got ${edits ? edits.length : 'null'}`);
    await applyDocEdits(doc.uri, edits);
}

suite('TLA+ Document Formatter Test Suite', () => {
    suite('extractModuleName', () => {
        test('Extracts module name from standard header', () => {
            const text = '---- MODULE MySpec ----\nVARIABLE x\n====';
            assert.strictEqual(extractModuleName(text), 'MySpec');
        });

        test('Extracts module name with multiple dashes', () => {
            const text = '---------- MODULE TestModule ----------\n====';
            assert.strictEqual(extractModuleName(text), 'TestModule');
        });

        test('Returns null for text without module declaration', () => {
            const text = 'VARIABLE x\nx == 1';
            assert.strictEqual(extractModuleName(text), null);
        });

        test('Extracts module name with underscores', () => {
            const text = '---- MODULE My_Spec_V2 ----\n====';
            assert.strictEqual(extractModuleName(text), 'My_Spec_V2');
        });

        test('Extracts first module name when multiple present', () => {
            const text = '---- MODULE First ----\n---- MODULE Second ----\n====';
            assert.strictEqual(extractModuleName(text), 'First');
        });

        test('Ignores MODULE keyword in comments', () => {
            const text = '\\* Notes: MODULE Fake\n---- MODULE RealSpec ----\n====';
            assert.strictEqual(extractModuleName(text), 'RealSpec');
        });
    });

    suite('Document formatting', () => {
        let tempDir: string;

        suiteSetup(async () => {
            // Trigger extension activation by opening a tlaplus document.
            const doc = await vscode.workspace.openTextDocument({ language: 'tlaplus' });
            await vscode.window.showTextDocument(doc);
            await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
        });

        setup(() => {
            tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-fmt-test-'));
        });

        teardown(async () => {
            await vscode.commands.executeCommand('workbench.action.closeActiveEditor');
            if (fs.existsSync(tempDir)) {
                fs.rmSync(tempDir, { recursive: true, force: true });
            }
        });

        test('Formats a saved TLA+ file', async function() {
            const isWin = process.platform === 'win32';
            this.timeout(isWin ? 60000 : 30000);

            const filePath = path.join(tempDir, 'HourClock.tla');
            fs.writeFileSync(filePath, UNFORMATTED, 'utf-8');

            const doc = await vscode.workspace.openTextDocument(filePath);
            if (doc.languageId !== 'tlaplus') {
                await vscode.languages.setTextDocumentLanguage(doc, 'tlaplus');
            }
            await vscode.window.showTextDocument(doc);

            await formatDocument(doc);
            assert.strictEqual(doc.getText(), EXPECTED);
        });

        test('Formats an unsaved TLA+ document', async function() {
            const isWin = process.platform === 'win32';
            this.timeout(isWin ? 60000 : 30000);

            const doc = await vscode.workspace.openTextDocument({ language: 'tlaplus', content: UNFORMATTED });
            await vscode.window.showTextDocument(doc);

            await formatDocument(doc);
            assert.strictEqual(doc.getText(), EXPECTED);
        });

        test('Formats unsaved buffer modifications of a saved file', async function() {
            const isWin = process.platform === 'win32';
            this.timeout(isWin ? 60000 : 30000);

            // Save a minimal placeholder to disk.
            const filePath = path.join(tempDir, 'HourClock.tla');
            fs.writeFileSync(filePath, '---- MODULE HourClock ----\n====\n', 'utf-8');

            const doc = await vscode.workspace.openTextDocument(filePath);
            if (doc.languageId !== 'tlaplus') {
                await vscode.languages.setTextDocumentLanguage(doc, 'tlaplus');
            }
            await vscode.window.showTextDocument(doc);

            // Replace the buffer with unformatted content without saving.
            await replaceDocContents(doc, UNFORMATTED);
            assert.ok(doc.isDirty, 'Document should have unsaved changes');

            await formatDocument(doc);
            assert.strictEqual(doc.getText(), EXPECTED);
        });

        test('Does not format when formatter is disabled', async function() {
            const isWin = process.platform === 'win32';
            this.timeout(isWin ? 60000 : 30000);

            const config = vscode.workspace.getConfiguration();
            await config.update('tlaplus.formatter.enabled', false, vscode.ConfigurationTarget.Global);

            try {
                const doc = await vscode.workspace.openTextDocument({ language: 'tlaplus', content: UNFORMATTED });
                await vscode.window.showTextDocument(doc);

                const edits = await vscode.commands.executeCommand<vscode.TextEdit[]>(
                    'vscode.executeFormatDocumentProvider',
                    doc.uri,
                    { insertSpaces: true, tabSize: 4 } as vscode.FormattingOptions
                );

                const noEdits = !edits || edits.length === 0;
                assert.ok(noEdits, `Expected no edits when formatter is disabled but got ${edits?.length}`);
                assert.strictEqual(doc.getText(), UNFORMATTED, 'Document should remain unchanged');
            } finally {
                await config.update('tlaplus.formatter.enabled', undefined, vscode.ConfigurationTarget.Global);
            }
        });
    });
});
