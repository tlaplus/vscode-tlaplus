import * as assert from 'assert';
import { parseNDJSON } from '../../../src/parsers/ndjson';

suite('NDJSON Parser Test Suite', () => {
    test('should parse valid NDJSON data', () => {
        const input = `{"traces":100,"duration":60,"generated":1000,"distinct":500}
{"traces":200,"duration":120,"generated":2000,"distinct":800}`;

        const result = parseNDJSON(input);

        assert.strictEqual(result.length, 2);
        assert.strictEqual(result[0].traces, 100);
        assert.strictEqual(result[0].duration, 60);
        assert.strictEqual(result[0].generated, 1000);
        assert.strictEqual(result[0].distinct, 500);

        assert.strictEqual(result[1].traces, 200);
        assert.strictEqual(result[1].duration, 120);
        assert.strictEqual(result[1].generated, 2000);
        assert.strictEqual(result[1].distinct, 800);
    });

    test('should handle empty input', () => {
        const result = parseNDJSON('');
        assert.strictEqual(result.length, 0);
    });

    test('should handle whitespace-only input', () => {
        const result = parseNDJSON('   \n  \n  ');
        assert.strictEqual(result.length, 0);
    });

    test('should skip invalid JSON lines', () => {
        const input = `{"traces":100,"duration":60,"generated":1000,"distinct":500}
invalid json line
{"traces":200,"duration":120,"generated":2000,"distinct":800}`;

        const result = parseNDJSON(input);
        assert.strictEqual(result.length, 2);
    });

    test('should handle missing fields with defaults', () => {
        const input = `{"traces":100}
{"duration":120,"generated":2000}`;

        const result = parseNDJSON(input);
        assert.strictEqual(result.length, 2);

        // First line has traces but missing other fields
        assert.strictEqual(result[0].traces, 100);
        assert.strictEqual(result[0].duration, 0);
        assert.strictEqual(result[0].generated, 0);
        assert.strictEqual(result[0].distinct, 0);

        // Second line missing traces
        assert.strictEqual(result[1].traces, 0);
        assert.strictEqual(result[1].duration, 120);
        assert.strictEqual(result[1].generated, 2000);
        assert.strictEqual(result[1].distinct, 0);
    });

    test('should parse real TLC output format', () => {
        const input = '{"traces":34008,"duration":60,"generated":4494285,"behavior":{"actions":{},"id":34001},' +
            '"worker":0,"distinct":114033,"distinctvalues":{"view":12906},"retries":1072284,' +
            '"actions":{"TLCInit":3863},"levelmean":40,"levelvariance":3598}';

        const result = parseNDJSON(input);
        assert.strictEqual(result.length, 1);
        assert.strictEqual(result[0].traces, 34008);
        assert.strictEqual(result[0].duration, 60);
        assert.strictEqual(result[0].generated, 4494285);
        assert.strictEqual(result[0].distinct, 114033);
    });
});