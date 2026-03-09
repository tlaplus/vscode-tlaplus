import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import { ParseModuleTool, FileParameter } from '../../../src/lm/SANYTool';
import { DiagnosticsProjector } from '../../../src/services/diagnosticsProjector';
import { ParseService } from '../../../src/services/parseService';

suite('SANY Tool cancellation handling', () => {
    test('ParseModuleTool ignores a pre-cancelled token', async () => {
        let transpileCalls = 0;
        let parseSpecCalls = 0;
        const parseService = {
            transpilePlusCal: async () => {
                transpileCalls++;
                throw new Error('should not be called');
            },
            parseSpec: async () => {
                parseSpecCalls++;
                throw new Error('should not be called');
            },
        } as unknown as ParseService;
        const diagnosticsProjector = {
            project: () => undefined,
        } as unknown as DiagnosticsProjector;

        const tool = new ParseModuleTool(parseService, diagnosticsProjector);
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
    });
});
