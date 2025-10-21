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

        // Wait for process to finish
        await new Promise((resolve) => {
            procInfo.process.on('exit', () => {
                setTimeout(resolve, 100); // Give streams time to flush
            });
        });

        // Verify that mergedOutput captured output
        assert.ok(capturedOutput.length > 0, 'mergedOutput should capture process output');

        // The output should contain either:
        // 1. SANY error messages about undefined variables (proving stderr is merged)
        // 2. Java errors from stderr (if classpath issues exist in test environment)
        // Either way proves that stderr is being merged with stdout
        const hasErrorMessage = capturedOutput.includes('line 4, col 9 to line 4, col 9 of module ParseError') &&
                                capturedOutput.includes('Unknown operator: `x') &&
                                capturedOutput.includes('Linting of module ParseError') &&
                                capturedOutput.includes('*** Errors: 4');

        assert.ok(hasErrorMessage, `mergedOutput should contain error messages. Got: ${capturedOutput.substring(0, 300)}`);

        // If SANY ran successfully (not a Java classpath error), verify the actual error is captured
        if (capturedOutput.includes('SANY') && !capturedOutput.includes('ClassNotFoundException')) {
            const hasUndefinedVarError = capturedOutput.toLowerCase().includes('undefinedvar') ||
                                        capturedOutput.toLowerCase().includes('unknown') ||
                                        capturedOutput.toLowerCase().includes('identifier');
            assert.ok(hasUndefinedVarError,
                `Should capture SANY semantic errors about undefinedVar. Output: ${capturedOutput.substring(0, 500)}`);
        }
    });

});

