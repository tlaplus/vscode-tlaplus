import * as assert from 'assert';
import { tlcTraceToPuml } from '../../../src/generators/tlcTraceToPuml';

suite('tlcTraceToPuml Test Suite', () => {

    test('Returns null when no trace is found', () => {
        const output = '/\\ x = 42\n/\\ y = TRUE';
        const result = tlcTraceToPuml(output);
        assert.strictEqual(result, null);
    });

    test('Generates PlantUML from single-message trace', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "ReadReq", src |-> "CPU", dst |-> "LLC"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml, 'Expected non-null PlantUML output');
        assert.ok(puml.includes('@startuml'));
        assert.ok(puml.includes('@enduml'));
        assert.ok(puml.includes('participant "CPU"'));
        assert.ok(puml.includes('participant "LLC"'));
        assert.ok(puml.includes('ReadReq'));
    });

    test('Declares participants in discovery order', () => {
        const output = '/\\ _seqDiagramTrace = <<'
            + ' [msg |-> "R", src |-> "B", dst |-> "A"],'
            + ' [msg |-> "S", src |-> "C", dst |-> "B"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml);
        // B seen first (as src), then A (as dst), then C (as src of 2nd msg)
        const bIdx = puml.indexOf('participant "B"');
        const aIdx = puml.indexOf('participant "A"');
        const cIdx = puml.indexOf('participant "C"');
        assert.ok(bIdx < aIdx, 'B should be declared before A');
        assert.ok(aIdx < cIdx, 'A should be declared before C');
    });

    test('Includes autonumber directive', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "A", dst |-> "B"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml);
        assert.ok(puml.includes('autonumber'));
    });

    test('Includes title header when option provided', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "A", dst |-> "B"] >>';
        const puml = tlcTraceToPuml(output, { title: 'MyModel' });
        assert.ok(puml);
        assert.ok(puml.includes('header MyModel'));
    });

    test('Omits title header when not provided', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "A", dst |-> "B"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml);
        assert.ok(!puml.includes('header '));
    });

    test('Colors arrows when channel field present', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "A", dst |-> "B", ch |-> "data_ch"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml);
        // Channel colors from CHANNEL_PALETTE — arrow should contain a # color code
        assert.ok(puml.match(/-\[#[0-9a-fA-F]+\]>/), 'Arrow should have color');
        // Channel name should appear in label annotation
        assert.ok(puml.includes('data_ch'));
    });

    test('Auto-colors arrows by message type when no channel field', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "A", dst |-> "B"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml);
        // With no explicit ch field, the msg type ("R") is used as the channel key
        // so the arrow should still get a color from the palette
        assert.ok(puml.match(/-\[#[0-9a-fA-F]+\]>/), 'Arrow should have auto-assigned color');
        // Label should be colored but without channel annotation (no \\n<size:9>)
        assert.ok(puml.includes('<b>R</b>'));
        assert.ok(!puml.includes('<size:9>'), 'Should not show channel annotation when auto-colored by msg');
    });

    test('Respects custom trace variable name', () => {
        const output = '/\\ msgs = << [msg |-> "R", src |-> "X", dst |-> "Y"] >>';
        // Default trace variable won't find it
        assert.strictEqual(tlcTraceToPuml(output), null);
        // Custom variable name
        const puml = tlcTraceToPuml(output, { traceVariable: 'msgs' });
        assert.ok(puml);
        assert.ok(puml.includes('participant "X"'));
    });

    test('Generates concurrent regions from multiple dump traces', () => {
        // Two terminal states with different message orderings → concurrent region
        const dump = [
            'State 1:',
            '/\\ _seqDiagramTrace = << [msg |-> "A", src |-> "P", dst |-> "Q"],'
                + ' [msg |-> "B", src |-> "R", dst |-> "S"] >>',
            '/\\ flow_complete = TRUE',
            '',
            'State 2:',
            '/\\ _seqDiagramTrace = << [msg |-> "B", src |-> "R", dst |-> "S"],'
                + ' [msg |-> "A", src |-> "P", dst |-> "Q"] >>',
            '/\\ flow_complete = TRUE',
        ].join('\n');

        const puml = tlcTraceToPuml('', { dumpText: dump });
        assert.ok(puml, 'Expected non-null PlantUML for dump with two orderings');
        assert.ok(puml.includes('\npar '), 'Reordered traces should produce a par block');
        assert.ok(puml.includes('Chain 1'));
        assert.ok(puml.includes('Chain 2'));
    });

    test('Single dump trace produces sequential output (no par)', () => {
        const dump = [
            'State 1:',
            '/\\ _seqDiagramTrace = << [msg |-> "A", src |-> "P", dst |-> "Q"],'
                + ' [msg |-> "B", src |-> "R", dst |-> "S"] >>',
            '/\\ flow_complete = TRUE',
        ].join('\n');

        const puml = tlcTraceToPuml('', { dumpText: dump });
        assert.ok(puml);
        assert.ok(!puml.includes('\npar '), 'Single trace should not have par blocks');
    });

    test('Sanitizes participant names to valid PlantUML aliases', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "CPU-0", dst |-> "L2.Cache"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml);
        // Aliases should replace non-alphanumeric chars with underscore
        assert.ok(puml.includes('participant "CPU-0" as CPU_0'));
        assert.ok(puml.includes('participant "L2.Cache" as L2_Cache'));
    });

    test('Includes skinparam settings', () => {
        const output = '/\\ _seqDiagramTrace = << [msg |-> "R", src |-> "A", dst |-> "B"] >>';
        const puml = tlcTraceToPuml(output);
        assert.ok(puml);
        assert.ok(puml.includes('skinparam backgroundColor transparent'));
        assert.ok(puml.includes('skinparam sequenceMessageAlign center'));
    });
});
