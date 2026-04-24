import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as os from 'os';
import { spawnSync } from 'child_process';

suite('Export Module to PDF Integration Tests', () => {
    let tempDir: string;
    const isWin = process.platform === 'win32';

    // avoid failing if the developer doesn't have pdflatex
    function hasPdfLatex(): boolean {
        const result = spawnSync('pdflatex', ['--version'], { stdio: 'ignore' });
        return result.status === 0;
    }

    setup(() => {
        tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-pdf-test-'));
    });

    teardown(() => {
        if (fs.existsSync(tempDir)) {
            fs.rmSync(tempDir, { recursive: true, force: true });
        }
    });

    test('Generates PDF from a TLA+ module', async function () {
        if (!hasPdfLatex()) {
            this.skip();
        }
        this.timeout(isWin ? 120000 : 60000);

        const moduleName = 'TestModule';
        const filePath = path.join(tempDir, `${moduleName}.tla`);
        const texPath = path.join(tempDir, `${moduleName}.tex`);
        const pdfPath = path.join(tempDir, `${moduleName}.pdf`);

        fs.writeFileSync(filePath, [
            `---- MODULE ${moduleName} ----`,
            'Init == TRUE',
            'Next == TRUE',
            '===='
        ].join('\n') + '\n', 'utf-8');

        const doc = await vscode.workspace.openTextDocument(filePath);
        assert.strictEqual(doc.languageId, 'tlaplus', 'Document should be recognized as TLA+');
        await vscode.window.showTextDocument(doc);

        // executeCommand resolves only after the PDF has been written.
        await vscode.commands.executeCommand('tlaplus.exportToPdf');

        assert.ok(fs.existsSync(texPath), `.tex file should exist at ${texPath} after tla2tex step`);
        assert.ok(fs.existsSync(pdfPath), `PDF should be generated at ${pdfPath}`);
        assert.ok(fs.statSync(pdfPath).size > 0, 'PDF file should not be empty');
    });
});

