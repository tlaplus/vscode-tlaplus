import * as assert from 'assert';
import { beforeEach } from 'mocha';
import { CheckStatus, getStatusName, findChanges, Change, ValueKey, Value,
    CollectionValue, StructureValue} from '../../../src/model/check';
import { v, set, seq, struct } from '../shortcuts';

const ROOT = 'root';

suite('Check Model Test Suite', () => {
    beforeEach(() => {
        Value.switchIdsOff();
    });

    test('Throws when trying to get undefined status name', () => {
        const nonexistentStatus = Object.values(CheckStatus).length + 100;
        assert.throws(() => getStatusName(nonexistentStatus), Error);
    });

    test('All check statuses have names', () => {
        const statuses: CheckStatus[] = Object.values(CheckStatus)
            .filter(x => typeof x === 'number')
            .map(x => x as CheckStatus);
        statuses.forEach(s => getStatusName(s));
    });

    test('Handles unchanged structure', () => {
        assertChanges(
            struct(ROOT, v('bar', 'BAR'), v('foo', 'FOO')),
            struct(ROOT, v('bar', 'BAR'), v('foo', 'FOO')),
            structX(ROOT, Change.NOT_CHANGED,
                vX('bar', Change.NOT_CHANGED, 'BAR'),
                vX('foo', Change.NOT_CHANGED, 'FOO')
            )
        );
    });

    test('Detects structure primitive item change', () => {
        assertChanges(
            struct(ROOT, v('bar', 'BAR'), v('baz', 'BAZ'), v('foo', 'FOO')),
            struct(ROOT, v('bar', 'BAR'), v('baz', 'BAZUKA'), v('foo', 'FOO')),
            structX(ROOT, Change.MODIFIED,
                vX('bar', Change.NOT_CHANGED, 'BAR'),
                vX('baz', Change.MODIFIED, 'BAZUKA'),
                vX('foo', Change.NOT_CHANGED, 'FOO')
            )
        );
    });

    test('Detects new items in struct', () => {
        assertChanges(
            struct(ROOT, v('bar', 'BAR'), v('foo', 'FOO')),
            struct(ROOT, v('bar', 'BAR'), v('baz', 'BAZ'), v('foo', 'FOO')),
            structX(ROOT, Change.MODIFIED,
                vX('bar', Change.NOT_CHANGED, 'BAR'),
                vX('baz', Change.ADDED, 'BAZ'),
                vX('foo', Change.NOT_CHANGED, 'FOO')
            )
        );
    });

    test('Detects deleted items in struct', () => {
        const expected = structX(ROOT, Change.MODIFIED,
            vX('bar', Change.NOT_CHANGED, 'BAR'),
            vX('foo', Change.NOT_CHANGED, 'FOO'));
        expected.addDeletedItems([v('baz', 'BAZ')]);
        assertChanges(
            struct(ROOT, v('bar', 'BAR'), v('baz', 'BAZ'), v('foo', 'FOO')),
            struct(ROOT, v('bar', 'BAR'), v('foo', 'FOO')),
            expected
        );
    });

    test('Handles unchanged sequence', () => {
        assertChanges(
            seq(ROOT, v(1, 'foo'), v(2, 'bar')),
            seq(ROOT, v(1, 'foo'), v(2, 'bar')),
            seqX(ROOT, Change.NOT_CHANGED,
                vX(1, Change.NOT_CHANGED, 'foo'),
                vX(2, Change.NOT_CHANGED, 'bar')
            )
        );
    });

    test('Detects sequence primitive item change', () => {
        assertChanges(
            seq(ROOT, v(1, '11'), v(2, '22'), v(3, '33')),
            seq(ROOT, v(1, '11'), v(2, '77'), v(3, '33')),
            seqX(ROOT, Change.MODIFIED,
                vX(1, Change.NOT_CHANGED, '11'),
                vX(2, Change.MODIFIED, '77'),
                vX(3, Change.NOT_CHANGED, '33')
            )
        );
    });

    test('Handles unchanged set', () => {
        assertChanges(
            set(ROOT, v(1, 'foo'), v(2, 'bar')),
            set(ROOT, v(1, 'foo'), v(2, 'bar')),
            setX(ROOT, Change.NOT_CHANGED,
                vX(1, Change.NOT_CHANGED, 'foo'),
                vX(2, Change.NOT_CHANGED, 'bar')
            )
        );
    });

    test('Detects set primitive item change', () => {
        assertChanges(
            set(ROOT, v(1, 'foo'), v(2, 'bar'), v(3, 'baz')),
            set(ROOT, v(1, 'foo'), v(2, 'baroque'), v(3, 'baz')),
            setX(ROOT, Change.MODIFIED,
                vX(1, Change.NOT_CHANGED, 'foo'),
                vX(2, Change.MODIFIED, 'baroque'),
                vX(3, Change.NOT_CHANGED, 'baz')
            )
        );
    });

    test('Propagates modification flag to the top', () => {
        assertChanges(
            struct(ROOT,
                v('bar', 'BAR'),
                seq('foo',
                    v(1, 'one'),
                    v(2, 'two'))),
            struct(ROOT,
                v('bar', 'BAR'),
                seq('foo',
                    v(1, 'one'),
                    v(2, 'three'))),
            structX(ROOT, Change.MODIFIED,
                vX('bar', Change.NOT_CHANGED, 'BAR'),
                seqX('foo', Change.MODIFIED,
                    vX(1, Change.NOT_CHANGED, 'one'),
                    vX(2, Change.MODIFIED, 'three')))
        );
    });

    test('Finds subitem by ID', () => {
        Value.switchIdsOn();
        const varOne = v(1, 'one');
        const root = struct(ROOT,
            v('bar', 'BAR'),
            seq('foo',
                varOne,
                v(2, 'two')));
        const found = root.findItem(varOne.id);
        if (found) {
            assert.equal(found.id, varOne.id);
        } else {
            assert.fail('Value not found by ID');
        }
    });

    test('Skips deleted items when searching by ID', () => {
        Value.switchIdsOn();
        const varOne = vX(1, Change.DELETED, 'one');
        const root = struct(ROOT,
            v('bar', 'BAR'),
            seq('foo',
                varOne,
                v(2, 'two')));
        const found = root.findItem(varOne.id);
        assert.equal(typeof found, 'undefined');
    });
});

function assertChanges(prev: CollectionValue, state: CollectionValue, expect: CollectionValue) {
    findChanges(prev, state);
    assert.deepEqual(state, expect);
}

function vX(key: ValueKey, change: Change, str: string) {
    const value = v(key, str);
    value.changeType = change;
    return value;
}

function seqX(key: ValueKey, change: Change, ...items: Value[]) {
    const value = seq(key, ...items);
    value.changeType = change;
    return value;
}

function setX(key: ValueKey, change: Change, ...items: Value[]) {
    const value = set(key, ...items);
    value.changeType = change;
    return value;
}

function structX(key: ValueKey, change: Change, ...items: Value[]) {
    const value = new StructureValue(key, items, true);
    value.changeType = change;
    return value;
}
