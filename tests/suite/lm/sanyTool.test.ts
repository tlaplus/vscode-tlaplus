import * as assert from 'assert';
import * as path from 'path';
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
});
