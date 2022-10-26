import * as assert from 'assert';
import { before } from 'mocha';
import { parseVariableValue } from '../../../src/parsers/tlcValues';
import { Value } from '../../../src/model/check';
import { v, set, seq, struct, n } from '../shortcuts';

const ROOT = 'root';

suite('TLC Values Output Parser Test Suite', () => {
    before(() => {
        Value.switchIdsOff();
    });

    test('Parses primitive number values', () => {
        for (const val of ['0', '9', '3994829384736', '-1', '-392832']) {
            assertValue([val], v(ROOT, val), `Failed to parse primitive number value: ${val}`);
        }
    });

    test('Parses primitive boolean values', () => {
        for (const val of ['TRUE', 'FALSE']) {
            assertValue([val], v(ROOT, val), `Failed to parse primitive boolean value: ${val}`);
        }
    });

    test('Parses primitive string values', () => {
        for (const val of ['""', '"Hello, string"', '"How about \\"escaped\\" symbols \\\\?"']) {
            assertValue([val], v(ROOT, val), `Failed to parse primitive string value: ${val}`);
        }
    });

    test('Parses ranges', () => {
        for (const val of ['0..72', '-4..-1', '0..0']) {
            assertValue([val], v(ROOT, val), `Failed to parse range value: ${val}`);
        }
    });

    test('Parses empty set', () => {
        assertValue(['{}'], set(ROOT));
    });

    test('Parses nested sets', () => {
        assertValue(['{{{0}}}'], set(ROOT, set(1, set(1, v(1, '0')))));
    });

    test('Parses set of primitives', () => {
        assertValue(['{1, TRUE, "set"}'], set(ROOT, v(1, '1'), v(2, 'TRUE'), v(3, '"set"')));
    });

    test('Parses set with collections', () => {
        assertValue(
            ['{<<5>>, [a |-> "A"], {9}}'],
            set(ROOT,
                seq(1, v(1, '5')),
                struct(2, v('a', '"A"')),
                set(3, v(1, '9'))
            ));
    });

    test('Parses empty sequence', () => {
        assertValue(['<<>>'], seq(ROOT));
    });

    test('Parses nested sequences', () => {
        assertValue(['<<<<<<8>>>>>>'], seq(ROOT, seq(1, seq(1, v(1, '8')))));
    });

    test('Parses sequence of primitives', () => {
        assertValue(
            ['<<19, FALSE, "sequence">>'],
            seq(ROOT, v(1, '19'), v(2, 'FALSE'), v(3, '"sequence"'))
        );
    });

    test('Parses sequence with collections', () => {
        assertValue(
            ['<<[ p |-> 8 ], <<7>>, {"a"}>>'],
            seq(ROOT,
                struct(1, v('p', '8')),
                seq(2, v(1, '7')),
                set(3, v(1, '"a"'))
            )
        );
    });

    test('Parses empty structure', () => {
        assertValue(['[]'], struct(ROOT));
    });

    test('Parses nested structures', () => {
        assertValue(
            ['[ a |-> [ b |-> [ hello |-> "world" ]]]'],
            struct(ROOT, struct('a', struct('b', v('hello', '"world"'))))
        );
    });

    test('Parses structure with primitives', () => {
        assertValue(
            ['[ foo |-> 84, bar |-> TRUE, baz |-> "BAZ" ]'],
            struct(ROOT, v('foo', '84'), v('bar', 'TRUE'), v('baz', '"BAZ"'))
        );
    });

    test('Parses structure with var-values', () => {
        assertValue(
            ['[ foo |-> bar ]'],
            struct(ROOT, n('foo', 'bar'))
        );
    });

    test('Parses structure with collections', () => {
        assertValue(
            ['[ foo |-> <<84>>, bar |-> {TRUE}, baz |-> [ e |-> 0 ] ]'],
            struct(ROOT,
                seq('foo', v(1, '84')),
                set('bar', v(1, 'TRUE')),
                struct('baz', v('e', '0'))
            )
        );
    });

    test('Parses multiline collections', () => {
        const lines = [
            '[ num |-> 10,',
            '  eng |-> "ten",',
            '  ger |-> "zehn"]'
        ];
        const expect = struct(ROOT,
            v('num', '10'),
            v('eng', '"ten"'),
            v('ger', '"zehn"')
        );
        assertValue(lines, expect);
    });

    test('Formats simple values without keys', () => {
        assertFormat(v('foo', '"bar"'), '', ['"bar"']);
        assertFormat(v('bar', '10'), '', ['10']);
        assertFormat(v('baz', 'FALSE'), '', ['FALSE']);
        assertFormat(v(4, '5'), '', ['5']);
    });

    test('Formats simple values without indentation', () => {
        assertFormat(v('foo', '"FOO"'), '    ', ['"FOO"']);
        assertFormat(v('bar', '10'), '  ', ['10']);
    });

    test('Formats simple sequences', () => {
        assertFormat(seq(ROOT), '  ', ['<<>>']);
        assertFormat(seq(ROOT, v(1, '1'), v(2, '2'), v(3, '3')), '', ['<<1, 2, 3>>']);
        assertFormat(
            seq(ROOT, v(1, '10'), v(2, '20'), struct(3), v(4, '"some long-long-long string to exceed threshold"')),
            '', [
                '<<',
                '  10, ',
                '  20, ',
                '  [], ',
                '  "some long-long-long string to exceed threshold"',
                '>>'
            ]
        );
    });

    test('Formats simple sets', () => {
        assertFormat(set(ROOT), '  ', ['{}']);
        assertFormat(set(ROOT, v(1, '1'), v(2, '2'), v(3, '3')), '', ['{1, 2, 3}']);
        assertFormat(
            set(ROOT, v(1, '10'), v(2, '20'), struct(3), v(4, '"some long-long-long string to exceed threshold"')),
            '', [
                '{',
                '  10, ',
                '  20, ',
                '  [], ',
                '  "some long-long-long string to exceed threshold"',
                '}'
            ]
        );
    });
});

function assertValue(lines: string[], expected: Value, message?: string) {
    const value = parseVariableValue(ROOT, lines);
    assert.deepEqual(value, expected, message);
}

function assertFormat(value: Value, indent: string, expect: string[]) {
    assert.equal(value.format(indent), expect.join('\n'));
}
