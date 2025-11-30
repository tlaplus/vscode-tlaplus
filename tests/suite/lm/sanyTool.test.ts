import * as assert from 'assert';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import * as vscode from 'vscode';
import { DCollection } from '../../../src/diagnostic';
import { SanyData } from '../../../src/parsers/sany';
import { ParseModuleTool, FileParameter } from '../../../src/lm/SANYTool';
import * as parseModule from '../../../src/commands/parseModule';

suite('SANY Tool cancellation handling', () => {
    test('ParseModuleTool ignores a pre-cancelled token', async () => {
        const parseModuleMutable = parseModule as unknown as {
            transpilePlusCal: typeof parseModule.transpilePlusCal;
            parseSpec: typeof parseModule.parseSpec;
        };
        const originalTranspile = parseModuleMutable.transpilePlusCal;
        const originalParseSpec = parseModuleMutable.parseSpec;

        let transpileCalls = 0;
        let parseSpecCalls = 0;

        parseModuleMutable.transpilePlusCal = async () => {
            transpileCalls++;
            return new DCollection();
        };

        parseModuleMutable.parseSpec = async () => {
            parseSpecCalls++;
            return new SanyData();
        };

        try {
            const tool = new ParseModuleTool();
            const cts = new vscode.CancellationTokenSource();
            cts.cancel();

            const filePath = path.join(__dirname, 'FakeSpec.tla');
            const options = {
                toolInvocationToken: undefined,
                input: {
                    fileName: filePath
                }
            } as unknown as vscode.LanguageModelToolInvocationOptions<FileParameter>;

            const result = await tool.invoke(options, cts.token);

            assert.strictEqual(
                transpileCalls,
                0,
                'transpilePlusCal should not run when cancellation is requested ahead of time'
            );
            assert.strictEqual(
                parseSpecCalls,
                0,
                'parseSpec should not run when cancellation is requested ahead of time'
            );
            assert.strictEqual(result.content.length, 1, 'Expected a single cancellation message');
            const [part] = result.content;
            assert.ok(part instanceof vscode.LanguageModelTextPart, 'Result should be a text part');
            assert.strictEqual(
                (part as vscode.LanguageModelTextPart).value,
                `Parsing cancelled for ${filePath}.`
            );
        } finally {
            parseModuleMutable.transpilePlusCal = originalTranspile;
            parseModuleMutable.parseSpec = originalParseSpec;
        }
    });

    test('ParseModuleTool uses a temp copy and leaves the original file untouched', async () => {
        const parseModuleMutable = parseModule as unknown as {
            transpilePlusCal: typeof parseModule.transpilePlusCal;
            parseSpec: typeof parseModule.parseSpec;
        };
        const originalTranspile = parseModuleMutable.transpilePlusCal;
        const originalParseSpec = parseModuleMutable.parseSpec;

        const originalDir = await fs.promises.mkdtemp(path.join(os.tmpdir(), 'tlaplus-sany-orig-'));
        const originalPath = path.join(originalDir, 'Spec.tla');
        const originalContent = '---- MODULE Spec ----\n====\n';
        await fs.promises.writeFile(originalPath, originalContent, 'utf8');

        let transpilePath: string | undefined;
        let transpileDiagPath: string | undefined;
        let parseSpecPath: string | undefined;

        parseModuleMutable.transpilePlusCal = async (uri: vscode.Uri, _token?: vscode.CancellationToken, options?: { diagnosticFilePath?: string }) => {
            transpilePath = uri.fsPath;
            transpileDiagPath = options?.diagnosticFilePath;
            const dc = new DCollection();
            dc.addMessage(options?.diagnosticFilePath ?? uri.fsPath, new vscode.Range(0, 0, 0, 0), 'pluscal message');
            return dc;
        };

        parseModuleMutable.parseSpec = async (uri: vscode.Uri) => {
            parseSpecPath = uri.fsPath;
            const sd = new SanyData();
            sd.dCollection.addMessage(uri.fsPath, new vscode.Range(1, 0, 1, 0), 'sany message');
            return sd;
        };

        try {
            const tool = new ParseModuleTool();
            const options = {
                toolInvocationToken: undefined,
                input: { fileName: originalPath }
            } as unknown as vscode.LanguageModelToolInvocationOptions<FileParameter>;

            const result = await tool.invoke(options, new vscode.CancellationTokenSource().token);

            assert.ok(transpilePath, 'transpilePlusCal should have been called');
            assert.ok(parseSpecPath, 'parseSpec should have been called');
            assert.notStrictEqual(transpilePath, originalPath, 'transpilePlusCal must run on a temp copy');
            assert.notStrictEqual(parseSpecPath, originalPath, 'parseSpec must parse the temp copy');
            assert.strictEqual(transpileDiagPath, originalPath, 'diagnostics should be attributed to the original file');

            // Returned messages should reference the original path, not the temp copy
            assert.strictEqual(result.content.length, 2, 'Should surface both PlusCal and SANY diagnostics');
            const normalize = (p: string) => process.platform === 'win32' ? p.toLowerCase() : p;
            result.content.forEach(part => {
                assert.ok(part instanceof vscode.LanguageModelTextPart, 'Each result should be a text part');
                const val = (part as vscode.LanguageModelTextPart).value;
                const nVal = normalize(val);
                assert.ok(nVal.includes(normalize(originalPath)), 'Diagnostics should point to the original file path');
                assert.ok(!nVal.includes(normalize(transpilePath!)), 'Diagnostics should not leak temp file paths');
            });

            // Original file should remain unchanged on disk
            const after = await fs.promises.readFile(originalPath, 'utf8');
            assert.strictEqual(after, originalContent, 'Original file content must not be modified');
        } finally {
            parseModuleMutable.transpilePlusCal = originalTranspile;
            parseModuleMutable.parseSpec = originalParseSpec;
            await fs.promises.rm(originalDir, { recursive: true, force: true });
        }
    });
});
