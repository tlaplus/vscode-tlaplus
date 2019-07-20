import * as assert from 'assert';
import { parseValueLines } from '../../../parsers/tlcValues';
import { PrimitiveValue, Value, SetValue, SequenceValue, StructureValue, StructureItem } from '../../../model/check';

suite('TLC Values Output Parser Test Suite', () => {

    test('Parses primitive number values', () => {
        for (const val of ['0', '9', '3994829384736', '-1', '-392832']) {
            assertValue([val], v(val), `Failed to parse primitive number value: ${val}`);
        }
    });

    test('Parses primitive boolean values', () => {
        for (const val of ['TRUE', 'FALSE']) {
            assertValue([val], v(val), `Failed to parse primitive boolean value: ${val}`);
        }
    });

    test('Parses primitive string values', () => {
        for (const val of ['""', '"Hello, string"', '"How about \\\"escaped\\\" symbols \\\\?"']) {
            assertValue([val], v(val), `Failed to parse primitive string value: ${val}`);
        }
    });

    test('Parses empty set', () => {
        assertValue(['{}'], set());
    });

    test('Parses nested sets', () => {
        assertValue(['{{{0}}}'], set(set(set(v('0')))));
    });

    test('Parses set of primitives', () => {
        assertValue(['{1, TRUE, "set"}'], set(v('1'), v('TRUE'), v('\"set\"')));
    });

    test('Parses set with collections', () => {
        assertValue(['{<<5>>, [a |-> \"A\"], {9}}'], set(seq(v('5')), struct(sit('a', v('"A"'))), set(v('9'))));
    });

    test('Parses empty sequence', () => {
        assertValue(['<<>>'], seq());
    });

    test('Parses nested sequences', () => {
        assertValue(['<<<<<<0>>>>>>'], seq(seq(seq(v('0')))));
    });

    test('Parses sequence of primitives', () => {
        assertValue(['<<19, FALSE, "sequence">>'], seq(v('19'), v('FALSE'), v('\"sequence\"')));
    });

    test('Parses sequence with collections', () => {
        assertValue(['<<[ p |-> 8 ], <<7>>, {"a"}>>'], seq(struct(sit('p', v('8'))), seq(v('7')), set(v('"a"'))));
    });

    test('Parses empty structure', () => {
        assertValue(['[]'], struct());
    });

    test('Parses neste structures', () => {
        assertValue(
            ['[ a |-> [ b |-> [ hello |-> "world" ]]]'],
            struct(sit('a', struct(sit('b', struct(sit('hello', v('"world"'))))))));
    });

    test('Parses structure with primitives', () => {
        assertValue(
            ['[ foo |-> 84, bar |-> TRUE, baz |-> "BAZ" ]'],
            struct(sit('foo', v('84')), sit('bar', v('TRUE')), sit('baz', v('"BAZ"'))));
    });

    test('Parses structure with collections', () => {
        assertValue(
            ['[ foo |-> <<84>>, bar |-> {TRUE}, baz |-> [ e |-> 0 ] ]'],
            struct(sit('foo', seq(v('84'))), sit('bar', set(v('TRUE'))), sit('baz', struct(sit('e', v('0'))))));
    });

    test('Parses multiline collections', () => {
        const lines = [
            '[ num |-> 10,',
            '  eng |-> "ten",',
            '  ger |-> "zehn"]'
        ];
        const expect = struct(
            sit('num', v('10')),
            sit('eng', v('"ten"')),
            sit('ger', v('"zehn"'))
        );
        assertValue(lines, expect);
    });

    test('Parses complex case', () => {
        const lines = [
            '{ 12,',
            '  [ key_1 |-> <<"one", "two">>,',
            '    key_2 |-> { 3, 4,',
            '              "five", TRUE},',
            '    key_3 |-> [',
            '          subkey_41 |-> <<',
            '     -299384>>',
            ' ]],',
            '<<{}>>,',
            ' "long long \\" string"',
            '{<<',
            '',
            '   [ foo |-> {TRUE} ]',
            '>>}}',
        ];
        const expect = set(
            v('12'),
            struct(
                sit('key_1', seq(v('"one"'), v('"two"'))),
                sit('key_2', set(v('3'), v('4'), v('"five"'), v('TRUE'))),
                sit('key_3', struct(sit('subkey_41', seq(v('-299384')))))
            ),
            seq(set()),
            v('"long long \\" string"'),
            set(seq(struct(sit('foo', set(v('TRUE')))))),
        );
        assertValue(lines, expect);
    });
});

function assertValue(lines: string[], expected: Value, message?: string) {
    const value = parseValueLines(lines);
    assert.deepEqual(value, expected, message);
}

function v(value: string): PrimitiveValue {
    return new PrimitiveValue(value);
}

function set(...values: Value[]): SetValue {
    return new SetValue(values);
}

function seq(...values: Value[]): SequenceValue {
    return new SequenceValue(values);
}

function struct(...values: StructureItem[]): StructureValue {
    return new StructureValue(values);
}

function sit(key: string, value: Value): StructureItem {
    return new StructureItem(key, value);
}
