import * as assert from 'assert';
import * as path from 'path';
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as os from 'os';

suite('Parse Module Stream Merging Tests', () => {
    let tempDir: string;
    let diagnosticCollection: vscode.DiagnosticCollection;

    setup(() => {
        tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-test-'));
        diagnosticCollection = vscode.languages.createDiagnosticCollection('parseModule-test');
    });

    teardown(() => {
        diagnosticCollection.clear();
        diagnosticCollection.dispose();
        if (fs.existsSync(tempDir)) {
            fs.rmSync(tempDir, { recursive: true, force: true });
        }
    });

    test('ToolProcessInfo merges stdout and stderr streams with syntax errors', async function() {
        this.timeout(10000);

        // This test verifies that our stream merging implementation works correctly
        // by checking that SANY error messages are captured in the mergedOutput stream
        //
        // The module below produces 4 semantic errors when parsed by SANY:
        // - Unknown operator: `x'
        // - Unknown operator: `y'
        // - Unknown operator: `undefinedVar' (appears twice)
        //
        // These errors verify that stderr is being merged with stdout.
        // and regardless of where they are printed, they should appear.

        const moduleName = 'ParseError';
        const filePath = path.join(tempDir, `${moduleName}.tla`);
        const fileContent = `---- MODULE ParseError ----
EXTENDS Naturals

Foo == (x \\in {42}) /\\ (y \\in Nat)

Init == undefinedVar
Next == undefinedVar

Spec == Init /\\ Next
====`;

        fs.writeFileSync(filePath, fileContent, 'utf-8');

        const { runSany } = await import('../../../src/tla2tools');
        const procInfo = await runSany(filePath);

        // Capture data from merged stream
        let capturedOutput = '';
        procInfo.mergedOutput.on('data', (chunk) => {
            capturedOutput += chunk.toString();
        });

        // Wait for stream to end
        await new Promise((resolve) => {
            procInfo.mergedOutput.once('end', resolve);
            if (procInfo.mergedOutput.readableEnded) {
                resolve(null);
            }
        });

        // Wait for 'close' event (ensures all file handles released)
        await new Promise((resolve) => {
            procInfo.process.once('close', resolve);
            if (procInfo.process.exitCode !== null) {
                resolve(null);
            }
        });

        // Verify that mergedOutput captured output
        assert.ok(capturedOutput.length > 0, 'mergedOutput should capture process output');

        // The output should contain SANY error messages (proving stderr is merged with stdout)
        const hasErrorMessage = capturedOutput.includes('line 4, col 9 to line 4, col 9 of module ParseError') &&
                                capturedOutput.includes('Unknown operator: `x') &&
                                capturedOutput.includes('Linting of module ParseError') &&
                                capturedOutput.includes('*** Errors: 4');

        const sampleOutput = capturedOutput.substring(0, 300);
        assert.ok(
            hasErrorMessage,
            `mergedOutput should contain error messages. Got: ${sampleOutput}`
        );

        // Verify the semantic errors are captured
        const hasUndefinedVarError = capturedOutput.toLowerCase().includes('undefinedvar') ||
                                    capturedOutput.toLowerCase().includes('unknown') ||
                                    capturedOutput.toLowerCase().includes('identifier');
        assert.ok(hasUndefinedVarError,
            `Should capture SANY semantic errors about undefinedVar. Output: ${capturedOutput.substring(0, 500)}`);
    });

});
