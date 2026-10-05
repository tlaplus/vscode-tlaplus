import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { DCollection } from '../../../src/diagnostic';
import { SanyData, SanyStdoutParser } from '../../../src/parsers/sany';
import { ParseModuleTool, FileParameter } from '../../../src/lm/SANYTool';
import * as parseModule from '../../../src/commands/parseModule';
import * as main from '../../../src/main';

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

suite('SANY Tool error reporting', () => {
    test('ParseModuleTool reports the 1-based line SANY printed', async () => {
        const specPath = '/Users/alice/TLA/foo.tla';
        const sanyStdout = [
            `Parsing file ${specPath}`,
            'Semantic processing of module foo',
            'Semantic errors:',
            '*** Errors: 1',
            '',
            'line 7, col 3 to line 7, col 9 of module foo',
            '',
            "Unknown operator: `FooBar'.",
            ''
        ];
        const sanyData = new SanyStdoutParser(sanyStdout).readAllSync();

        const parseModuleMutable = parseModule as unknown as {
            transpilePlusCal: typeof parseModule.transpilePlusCal;
            parseSpec: typeof parseModule.parseSpec;
        };
        const mainMutable = main as unknown as { getDiagnostic: typeof main.getDiagnostic };
        const originalTranspile = parseModuleMutable.transpilePlusCal;
        const originalParseSpec = parseModuleMutable.parseSpec;
        const originalGetDiagnostic = mainMutable.getDiagnostic;
        const diagnostics = vscode.languages.createDiagnosticCollection('sanyToolTest');

        parseModuleMutable.transpilePlusCal = async () => new DCollection();
        parseModuleMutable.parseSpec = async () => sanyData;
        mainMutable.getDiagnostic = () => diagnostics;

        try {
            const options = {
                toolInvocationToken: undefined,
                input: { fileName: specPath }
            } as unknown as vscode.LanguageModelToolInvocationOptions<FileParameter>;

            const result = await new ParseModuleTool().invoke(options, new vscode.CancellationTokenSource().token);

            const texts = result.content.map((part) => (part as vscode.LanguageModelTextPart).value);
            assert.deepStrictEqual(texts, [
                `Parsing of file ${specPath} failed at line 7 with error 'Unknown operator: \`FooBar'.'`
            ]);
        } finally {
            parseModuleMutable.transpilePlusCal = originalTranspile;
            parseModuleMutable.parseSpec = originalParseSpec;
            mainMutable.getDiagnostic = originalGetDiagnostic;
            diagnostics.dispose();
        }
    });
});
