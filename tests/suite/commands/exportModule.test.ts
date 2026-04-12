import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as os from 'os';
import { spawnSync } from 'child_process';

suite('Export Module to PDF Integration Tests', () => {
    let tempDir: string;
    const isWin = process.platform === 'win32';

    function hasPdfLatex(): boolean {
        const result = spawnSync('pdflatex', ['--version'], { stdio: 'ignore' });
        return result.status === 0;
    }

    function waitForStableFile(filePath: string, timeoutMs: number): Promise<boolean> {
        return new Promise((resolve) => {
            const deadline = Date.now() + timeoutMs;
            let lastSize = -1;
            let stableCount = 0;

            const poll = () => {
                if (Date.now() > deadline) {
                    resolve(false);
                    return;
                }
                if (fs.existsSync(filePath)) {
                    const size = fs.statSync(filePath).size;
                    if (size > 0 && size === lastSize) {
                        stableCount++;
                        if (stableCount >= 2) {
                            resolve(true);
                            return;
                        }
                    } else {
                        stableCount = 0;
                    }
                    lastSize = size;
                }
                setTimeout(poll, 500);
            };
            poll();
        });
    }

    setup(() => {
        tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-pdf-test-'));
    });

    teardown(async () => {
        await vscode.commands.executeCommand('workbench.action.closeAllEditors');
        // Retry cleanup to handle Windows file locks from background pdflatex
        for (let i = 0; i < 3; i++) {
            try {
                if (fs.existsSync(tempDir)) {
                    fs.rmSync(tempDir, { recursive: true, force: true });
                }
                break;
            } catch {
                await new Promise(r => setTimeout(r, 1000));
            }
        }
    });

    test('Generates PDF from a TLA+ module', async function() {
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

        // executeCommand resolves after generateTexFile completes (awaited),
        // but before generatePdfFile finishes (fire-and-forget)
        await vscode.commands.executeCommand('tlaplus.exportToPdf');

        assert.ok(fs.existsSync(texPath), `.tex file should exist at ${texPath} after tla2tex step`);

        // Wait for PDF to be fully written (stable size across polls)
        const pollTimeout = isWin ? 90000 : 30000;
        const ready = await waitForStableFile(pdfPath, pollTimeout);

        assert.ok(ready, `PDF should be generated at ${pdfPath}`);
        assert.ok(fs.statSync(pdfPath).size > 0, 'PDF file should not be empty');
    });
});
