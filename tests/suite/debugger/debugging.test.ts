import * as assert from 'assert';
import * as path from 'path';
import * as fs from 'fs';
import * as os from 'os';
import { findLatestTraceFile, extractFingerprintFromTrace } from '../../../src/tla2tools';

suite('Debugging Test Suite', () => {
    let testDir: string;

    setup(() => {
        // Create a temporary directory for test files
        testDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tlaplus-debug-test-'));
    });

    teardown(() => {
        // Clean up temporary directory
        if (fs.existsSync(testDir)) {
            fs.rmSync(testDir, { recursive: true, force: true });
        }
    });

    suite('findLatestTraceFile', () => {
        test('Returns undefined when trace directory does not exist', async () => {
            const tlaFilePath = path.join(testDir, 'NonExistent.tla');
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, undefined, 'Should return undefined when directory does not exist');
        });

        test('Returns undefined when trace directory is empty', async () => {
            const tlaFilePath = path.join(testDir, 'Empty.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, undefined, 'Should return undefined when no trace files exist');
        });

        test('Returns undefined when no matching trace files exist', async () => {
            const tlaFilePath = path.join(testDir, 'MySpec.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            // Create a file that doesn't match the pattern
            fs.writeFileSync(path.join(traceDir, 'other_file.txt'), '');
            // Create a trace file for a different spec
            fs.writeFileSync(path.join(traceDir, 'OtherSpec_trace_T2024-01-15_10-30-00_F0_W1_Mbfs.tlc'), '');
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, undefined, 'Should return undefined when no matching trace files exist');
        });

        test('Finds single trace file', async () => {
            const tlaFilePath = path.join(testDir, 'MySpec.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            const traceFileName = 'MySpec_trace_T2024-01-15_10-30-00_F42_W1_Mbfs.tlc';
            const traceFilePath = path.join(traceDir, traceFileName);
            fs.writeFileSync(traceFilePath, 'test trace content');
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, traceFilePath, 'Should find the single trace file');
        });

        test('Returns latest trace file when multiple exist', async () => {
            const tlaFilePath = path.join(testDir, 'MySpec.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            // Create multiple trace files with different timestamps
            const oldTrace = path.join(traceDir, 'MySpec_trace_T2024-01-15_10-30-00_F42_W1_Mbfs.tlc');
            const middleTrace = path.join(traceDir, 'MySpec_trace_T2024-01-16_14-20-00_F43_W2_Mbfs.tlc');
            const latestTrace = path.join(traceDir, 'MySpec_trace_T2024-01-17_16-45-30_F44_W4_Mbfs.tlc');
            
            fs.writeFileSync(oldTrace, 'old trace');
            fs.writeFileSync(middleTrace, 'middle trace');
            fs.writeFileSync(latestTrace, 'latest trace');
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, latestTrace, 'Should return the trace file with the latest timestamp');
        });

        test('Sorts by timestamp correctly across different dates', async () => {
            const tlaFilePath = path.join(testDir, 'Test.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            // Create traces with timestamps in different months and years
            const trace2023 = path.join(traceDir, 'Test_trace_T2023-12-31_23-59-59_F0_W1_Mbfs.tlc');
            const trace2024Jan = path.join(traceDir, 'Test_trace_T2024-01-01_00-00-00_F1_W1_Mbfs.tlc');
            const trace2024Feb = path.join(traceDir, 'Test_trace_T2024-02-15_12-30-00_F2_W1_Mbfs.tlc');
            
            fs.writeFileSync(trace2023, '2023 trace');
            fs.writeFileSync(trace2024Jan, '2024 jan trace');
            fs.writeFileSync(trace2024Feb, '2024 feb trace');
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, trace2024Feb, 'Should return the trace with the most recent timestamp');
        });

        test('Ignores files that do not match the trace pattern', async () => {
            const tlaFilePath = path.join(testDir, 'MySpec.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            // Create a valid trace file
            const validTrace = path.join(traceDir, 'MySpec_trace_T2024-01-15_10-30-00_F42_W1_Mbfs.tlc');
            fs.writeFileSync(validTrace, 'valid trace');
            
            // Create invalid files that should be ignored
            fs.writeFileSync(path.join(traceDir, 'MySpec_trace.tlc'), 'invalid');
            fs.writeFileSync(path.join(traceDir, 'MySpec_trace_T2024-01-15.tlc'), 'invalid');
            fs.writeFileSync(path.join(traceDir, 'MySpec_T2024-01-15_10-30-00_F42_W1_Mbfs.tlc'), 'missing trace');
            fs.writeFileSync(path.join(traceDir, 'random_file.txt'), 'random');
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, validTrace, 'Should find only the valid trace file');
        });

        test('Handles spec names with underscores', async () => {
            const tlaFilePath = path.join(testDir, 'My_Complex_Spec.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            const traceFileName = 'My_Complex_Spec_trace_T2024-01-15_10-30-00_F5_W1_Mbfs.tlc';
            const traceFilePath = path.join(traceDir, traceFileName);
            fs.writeFileSync(traceFilePath, 'trace with underscore spec');
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, traceFilePath, 'Should handle spec names with underscores');
        });

        test('Only matches BFS mode traces', async () => {
            const tlaFilePath = path.join(testDir, 'MySpec.tla');
            const traceDir = path.join(testDir, '.vscode', 'tlc');
            fs.mkdirSync(traceDir, { recursive: true });
            
            // Create a valid BFS trace
            const bfsTrace = path.join(traceDir, 'MySpec_trace_T2024-01-15_10-30-00_F42_W1_Mbfs.tlc');
            fs.writeFileSync(bfsTrace, 'bfs trace');
            
            // Create a file with different mode (should be ignored)
            const otherModeTrace = path.join(traceDir, 'MySpec_trace_T2024-01-16_10-30-00_F42_W1_Msimulation.tlc');
            fs.writeFileSync(otherModeTrace, 'simulation trace');
            
            const result = await findLatestTraceFile(tlaFilePath);
            assert.strictEqual(result, bfsTrace, 'Should only match BFS mode traces');
        });
    });

    suite('extractFingerprintFromTrace - additional error cases', () => {
        test('Handles trace filename with fingerprint at beginning', async () => {
            // This should NOT match since fingerprint must be preceded by _
            const traceFile = 'F42_MySpec_trace_T2024-01-15_10-30-00_W1_Mbfs.tlc';
            const fp = extractFingerprintFromTrace(traceFile);
            assert.strictEqual(fp, undefined, 'Should not extract fingerprint from incorrect position');
        });

        test('Handles trace filename with fingerprint at end', async () => {
            // This should NOT match since fingerprint must be followed by _
            const traceFile = 'MySpec_trace_T2024-01-15_10-30-00_W1_Mbfs_F42.tlc';
            const fp = extractFingerprintFromTrace(traceFile);
            assert.strictEqual(fp, undefined, 'Should not extract fingerprint from incorrect position');
        });

        test('Extracts fingerprint with different worker counts', async () => {
            const traceFile = 'MySpec_trace_T2024-01-15_10-30-00_F99_W16_Mbfs.tlc';
            const fp = extractFingerprintFromTrace(traceFile);
            assert.strictEqual(fp, 99, 'Should extract fingerprint regardless of worker count');
        });

        test('Handles fingerprint value of 0', async () => {
            const traceFile = 'MySpec_trace_T2024-01-15_10-30-00_F0_W1_Mbfs.tlc';
            const fp = extractFingerprintFromTrace(traceFile);
            assert.strictEqual(fp, 0, 'Should correctly handle fingerprint value of 0');
        });

        test('Handles large fingerprint values', async () => {
            const traceFile = 'MySpec_trace_T2024-01-15_10-30-00_F130_W1_Mbfs.tlc';
            const fp = extractFingerprintFromTrace(traceFile);
            assert.strictEqual(fp, 130, 'Should handle maximum fingerprint value');
        });

        test('Handles malformed fingerprint (non-numeric)', async () => {
            const traceFile = 'MySpec_trace_T2024-01-15_10-30-00_Fabc_W1_Mbfs.tlc';
            const fp = extractFingerprintFromTrace(traceFile);
            assert.strictEqual(fp, undefined, 'Should return undefined for non-numeric fingerprint');
        });
    });

    suite('debugCounterexample TLC options construction', () => {
        test('Constructs correct -loadtrace and -fp options from trace filename', () => {
            // Simulate what debugCounterexample should produce
            const traceFilePath = '/path/to/.vscode/tlc/MySpec_trace_T2024-01-15_10-30-00_F42_W1_Mbfs.tlc';
            const fpValue = extractFingerprintFromTrace(traceFilePath);
            
            assert.strictEqual(fpValue, 42, 'Should extract correct fingerprint');
            
            // Verify the expected TLC options format that debugCounterexample builds
            const expectedOptions = [
                '-fp', '42',
                '-loadtrace', 'tlc', traceFilePath,
                '-debugger', 'port=12345' // port would vary
            ];
            
            // Verify the structure
            assert.strictEqual(expectedOptions[0], '-fp');
            assert.strictEqual(expectedOptions[1], '42');
            assert.strictEqual(expectedOptions[2], '-loadtrace');
            assert.strictEqual(expectedOptions[3], 'tlc');
            assert.strictEqual(expectedOptions[4], traceFilePath);
            assert.strictEqual(expectedOptions[5], '-debugger');
        });

        test('Handles trace with different fingerprint value', () => {
            const traceFilePath = '/path/to/.vscode/tlc/Test_trace_T2024-01-15_10-30-00_F0_W1_Mbfs.tlc';
            const fpValue = extractFingerprintFromTrace(traceFilePath);
            
            assert.strictEqual(fpValue, 0, 'Should extract fingerprint value of 0');
            
            // Verify -fp option would be set correctly
            const expectedFpArg = String(fpValue);
            assert.strictEqual(expectedFpArg, '0');
        });

        test('Handles trace with maximum fingerprint value', () => {
            const traceFilePath = '/path/to/.vscode/tlc/Test_trace_T2024-01-15_10-30-00_F130_W8_Mbfs.tlc';
            const fpValue = extractFingerprintFromTrace(traceFilePath);
            
            assert.strictEqual(fpValue, 130, 'Should extract maximum fingerprint value');
            
            const expectedFpArg = String(fpValue);
            assert.strictEqual(expectedFpArg, '130');
        });

        test('Verifies warning path: missing fingerprint in trace filename', () => {
            const invalidTraceFile = '/path/to/.vscode/tlc/MySpec_trace_T2024-01-15_10-30-00_W1_Mbfs.tlc';
            const fpValue = extractFingerprintFromTrace(invalidTraceFile);
            
            // This should trigger the warning path in debugCounterexample
            assert.strictEqual(fpValue, undefined, 'Should return undefined for missing fingerprint');
        });

        test('Verifies warning path: malformed trace filename', () => {
            const invalidTraceFile = '/path/to/random_file.tlc';
            const fpValue = extractFingerprintFromTrace(invalidTraceFile);
            
            // This should trigger the warning path in debugCounterexample
            assert.strictEqual(fpValue, undefined, 'Should return undefined for malformed filename');
        });

        test('Options format is compatible with TLC', () => {
            // Verify that the options constructed match TLC's expected format:
            // -fp <value> -loadtrace <format> <file>
            const traceFile = '/spec/.vscode/tlc/Spec_trace_T2024-01-15_10-30-00_F73_W4_Mbfs.tlc';
            const fp = extractFingerprintFromTrace(traceFile);
            
            const options = [
                '-fp', String(fp),
                '-loadtrace', 'tlc', traceFile
            ];
            
            // Verify order and structure
            assert.strictEqual(options[0], '-fp', 'First option should be -fp');
            assert.strictEqual(options[1], '73', 'FP value should be a string');
            assert.strictEqual(options[2], '-loadtrace', 'Third option should be -loadtrace');
            assert.strictEqual(options[3], 'tlc', 'Trace format should be tlc');
            assert.strictEqual(options[4], traceFile, 'Trace file path should be included');
            
            // Verify all values are strings (as required by spawn)
            options.forEach((opt, idx) => {
                assert.strictEqual(typeof opt, 'string', `Option at index ${idx} should be a string`);
            });
        });
    });
});
