import * as assert from 'assert';
import { parseTlcTrace, parseAllTerminalTraces } from '../../../src/parsers/traceParser';

suite('Trace Parser Test Suite', () => {

    // ── parseTlcTrace ────────────────────────────────────────

    suite('parseTlcTrace', () => {
        test('Returns null when trace variable is absent', () => {
            const output = '/\\ x = 42\n/\\ y = TRUE';
            assert.strictEqual(parseTlcTrace(output, 'trace'), null);
        });

        test('Parses single-message trace', () => {
            const output = '/\\ _seqDiagramTrace = << [msg |-> "Req", src |-> "A", dst |-> "B"] >>';
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].msg, 'Req');
            assert.strictEqual(result[0].src, 'A');
            assert.strictEqual(result[0].dst, 'B');
            assert.strictEqual(result[0].ch, undefined);
        });

        test('Parses multi-message trace', () => {
            const output = [
                '/\\ _seqDiagramTrace = <<',
                '  [msg |-> "Req", src |-> "A", dst |-> "B"],',
                '  [msg |-> "Ack", src |-> "B", dst |-> "A"]',
                '>>',
            ].join('\n');
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result.length, 2);
            assert.strictEqual(result[0].msg, 'Req');
            assert.strictEqual(result[1].msg, 'Ack');
            assert.strictEqual(result[1].src, 'B');
            assert.strictEqual(result[1].dst, 'A');
        });

        test('Extracts channel field when present', () => {
            const output = '/\\ _seqDiagramTrace = << [msg |-> "Req", src |-> "A", dst |-> "B", ch |-> "data"] >>';
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result[0].ch, 'data');
        });

        test('Returns empty array for empty trace', () => {
            const output = '/\\ _seqDiagramTrace = <<  >>';
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result.length, 0);
        });

        test('Handles multi-line wrapping (whitespace collapsing)', () => {
            // TLC wraps long lines: the delimiter may be split across lines
            const output = [
                '/\\ _seqDiagramTrace = << [msg |-> "ReqA",',
                '               src |-> "CPU",',
                '               dst |-> "LLC"] >>',
            ].join('\n');
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].msg, 'ReqA');
            assert.strictEqual(result[0].src, 'CPU');
            assert.strictEqual(result[0].dst, 'LLC');
        });

        test('Uses last match when multiple states contain trace', () => {
            const output = [
                '/\\ _seqDiagramTrace = << [msg |-> "Old", src |-> "X", dst |-> "Y"] >>',
                '',
                '/\\ _seqDiagramTrace = << [msg |-> "New", src |-> "A", dst |-> "B"] >>',

            ].join('\n');
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].msg, 'New');
        });

        test('Respects custom trace variable name', () => {
            const output = '/\\ my_msgs = << [msg |-> "R", src |-> "X", dst |-> "Y"] >>';
            assert.strictEqual(parseTlcTrace(output, 'trace'), null);

            const result = parseTlcTrace(output, 'my_msgs');
            assert.ok(result);
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].msg, 'R');
        });

        test('Skips records with missing required fields', () => {
            const output = '/\\ _seqDiagramTrace = <<'
                + ' [msg |-> "R", src |-> "A"],'
                + ' [msg |-> "S", src |-> "A", dst |-> "B"] >>';
            const result = parseTlcTrace(output);
            assert.ok(result);
            // First record missing dst → skipped
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].msg, 'S');
        });

        test('Handles special characters in participant names', () => {
            const output = '/\\ _seqDiagramTrace = << [msg |-> "CacheReq", src |-> "CPU-0", dst |-> "L2.Cache"] >>';
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result[0].src, 'CPU-0');
            assert.strictEqual(result[0].dst, 'L2.Cache');
        });

        test('Parses ALIAS output (no /\\ prefix)', () => {
            const output = '_seqDiagramTrace = <<'
                + ' [msg |-> "MWr", ch |-> "pcie_req",'
                + ' src |-> "PCIe", dst |-> "HIOP"] >>';
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].msg, 'MWr');
            assert.strictEqual(result[0].ch, 'pcie_req');
        });

        test('Parses multi-state ALIAS output (last match wins)', () => {
            const output = [
                '_seqDiagramTrace = << >>',
                '',
                '_seqDiagramTrace = <<'
                    + ' [msg |-> "Req", src |-> "A", dst |-> "B"] >>',
            ].join('\n');
            const result = parseTlcTrace(output);
            assert.ok(result);
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].msg, 'Req');
        });
    });

    // ── parseAllTerminalTraces ───────────────────────────────

    suite('parseAllTerminalTraces', () => {
        function makeDumpBlock(stateNum: number, traceStr: string, done: boolean): string {
            return [
                `State ${stateNum}:`,
                `/\\ _seqDiagramTrace = ${traceStr}`,
                `/\\ flow_complete = ${done ? 'TRUE' : 'FALSE'}`,
            ].join('\n');
        }

        test('Returns empty array when no terminal states exist', () => {
            const dump = makeDumpBlock(1,
                '<< [msg |-> "R", src |-> "A", dst |-> "B"] >>', false);
            const result = parseAllTerminalTraces(dump);
            assert.strictEqual(result.length, 0);
        });

        test('Extracts single terminal trace', () => {
            const dump = [
                makeDumpBlock(1,
                    '<< [msg |-> "R", src |-> "A", dst |-> "B"] >>', false),
                makeDumpBlock(2,
                    '<< [msg |-> "R", src |-> "A", dst |-> "B"], [msg |-> "A", src |-> "B", dst |-> "A"] >>',
                    true),
            ].join('\n');
            const result = parseAllTerminalTraces(dump);
            assert.strictEqual(result.length, 1);
            assert.strictEqual(result[0].length, 2);
            assert.strictEqual(result[0][1].msg, 'A');
        });

        test('Deduplicates identical terminal traces', () => {
            const traceStr = '<< [msg |-> "R", src |-> "A", dst |-> "B"] >>';
            const dump = [
                makeDumpBlock(1, traceStr, true),
                makeDumpBlock(2, traceStr, true),
                makeDumpBlock(3, traceStr, true),
            ].join('\n');
            const result = parseAllTerminalTraces(dump);
            assert.strictEqual(result.length, 1);
        });

        test('Returns multiple distinct terminal traces', () => {
            const dump = [
                makeDumpBlock(1,
                    '<< [msg |-> "R1", src |-> "A", dst |-> "B"] >>', true),
                makeDumpBlock(2,
                    '<< [msg |-> "R2", src |-> "C", dst |-> "D"] >>', true),
            ].join('\n');
            const result = parseAllTerminalTraces(dump);
            assert.strictEqual(result.length, 2);
        });

        test('Respects custom done variable name', () => {
            const dump = [
                'State 1:',
                '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "A", dst |-> "B"] >>',
                '/\\ all_done = TRUE',
            ].join('\n');
            // Default done variable "flow_complete" won't match
            assert.strictEqual(parseAllTerminalTraces(dump).length, 0);
            // Custom done variable
            const result = parseAllTerminalTraces(dump, '_seqDiagramTrace', 'all_done');
            assert.strictEqual(result.length, 1);
        });

        test('Ignores states with empty traces', () => {
            const dump = [
                'State 1:',
                '/\\ _seqDiagramTrace = <<  >>',
                '/\\ flow_complete = TRUE',
            ].join('\n');
            const result = parseAllTerminalTraces(dump);
            assert.strictEqual(result.length, 0);
        });
    });
});
