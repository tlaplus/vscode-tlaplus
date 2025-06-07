import * as assert from 'assert';
import { beforeEach } from 'mocha';
import * as fc from 'fast-check';
import { Change, Value, SetValue, findChanges } from '../../../src/model/check';

suite('Set Diff Properties Test Suite', () => {
    beforeEach(() => {
        Value.switchIdsOff();
    });

    test('Property 1: should correctly identify added elements', () => {
        fc.assert(
            fc.property(
                fc.array(fc.string(), { minLength: 0, maxLength: 10 }),
                fc.array(fc.string(), { minLength: 0, maxLength: 10 }),
                (oldElements, newElements) => {
                    const oldSet = createTestSet(oldElements);
                    const newSet = createTestSet(newElements);

                    findChanges(oldSet, newSet);

                    const oldStrings = new Set(oldElements);
                    newSet.items.forEach(item => {
                        if (!oldStrings.has(item.str)) {
                            assert.strictEqual(item.changeType, Change.ADDED,
                                `Element "${item.str}" should be marked as ADDED`);
                        }
                    });
                }
            ),
            { numRuns: 1000, verbose: true }
        );
    });

    test('Property 2: should correctly identify deleted elements', () => {
        fc.assert(
            fc.property(
                fc.array(fc.string(), { minLength: 1, maxLength: 10 }),
                fc.array(fc.string(), { minLength: 0, maxLength: 10 }),
                (oldElements, newElements) => {
                    const oldSet = createTestSet(oldElements);
                    const newSet = createTestSet(newElements);

                    findChanges(oldSet, newSet);

                    // Count occurrences of each string in both arrays
                    const oldCounts = new Map<string, number>();
                    const newCounts = new Map<string, number>();

                    oldElements.forEach(e => oldCounts.set(e, (oldCounts.get(e) || 0) + 1));
                    newElements.forEach(e => newCounts.set(e, (newCounts.get(e) || 0) + 1));

                    // Calculate expected deletions based on count differences
                    const expectedDeleted: string[] = [];
                    oldCounts.forEach((oldCount, str) => {
                        const newCount = newCounts.get(str) || 0;
                        const deletions = Math.max(0, oldCount - newCount);
                        for (let i = 0; i < deletions; i++) {
                            expectedDeleted.push(str);
                        }
                    });

                    if (expectedDeleted.length > 0) {
                        assert.ok(newSet.deletedItems, 'deletedItems should be defined when elements are deleted');
                        const actualDeleted = newSet.deletedItems.map(i => i.str).sort();
                        assert.deepStrictEqual(actualDeleted, expectedDeleted.sort(),
                            'Deleted items do not match expected');
                    }
                }
            ),
            { numRuns: 1000, verbose: true }
        );
    });

    test('Property 3: should correctly identify unchanged elements', () => {
        fc.assert(
            fc.property(
                fc.array(fc.string(), { minLength: 1, maxLength: 10 }),
                fc.array(fc.string(), { minLength: 1, maxLength: 10 }),
                (oldElements, newElements) => {
                    const oldSet = createTestSet(oldElements);
                    const newSet = createTestSet(newElements);

                    findChanges(oldSet, newSet);

                    // Count occurrences in both arrays
                    const oldCounts = new Map<string, number>();
                    const newCounts = new Map<string, number>();

                    oldElements.forEach(e => oldCounts.set(e, (oldCounts.get(e) || 0) + 1));
                    newElements.forEach(e => newCounts.set(e, (newCounts.get(e) || 0) + 1));

                    // Track how many of each string we've seen in the new set
                    const seenCounts = new Map<string, number>();

                    newSet.items.forEach(item => {
                        const seenCount = (seenCounts.get(item.str) || 0) + 1;
                        seenCounts.set(item.str, seenCount);

                        const oldCount = oldCounts.get(item.str) || 0;

                        // This item should be NOT_CHANGED if we haven't exceeded the old count
                        if (seenCount <= oldCount) {
                            assert.strictEqual(item.changeType, Change.NOT_CHANGED,
                                `Element "${item.str}" (occurrence ${seenCount}/${oldCount}) should be NOT_CHANGED`);
                        } else {
                            // Otherwise it should be ADDED
                            assert.strictEqual(item.changeType, Change.ADDED,
                                `Element "${item.str}" (occurrence ${seenCount} > ${oldCount}) should be ADDED`);
                        }
                    });
                }
            ),
            { numRuns: 1000, verbose: true }
        );
    });

    test('Property 4: should handle reordered sets correctly', () => {
        fc.assert(
            fc.property(
                fc.uniqueArray(fc.string(), { minLength: 2, maxLength: 20 }),
                (elements) => {
                    const oldSet = createTestSet(elements);
                    // Create a shuffled version with same elements
                    const shuffled = [...elements].sort(() => Math.random() - 0.5);
                    const newSet = createTestSet(shuffled);

                    findChanges(oldSet, newSet);

                    // All elements should be unchanged
                    newSet.items.forEach(item => {
                        assert.strictEqual(item.changeType, Change.NOT_CHANGED,
                            `Element "${item.str}" in reordered set should be NOT_CHANGED`);
                    });

                    // No deleted items
                    assert.strictEqual(newSet.deletedItems, undefined,
                        'No items should be deleted when sets contain same elements');

                    // Set itself should not be modified
                    assert.strictEqual(newSet.changeType, Change.NOT_CHANGED,
                        'Set should not be marked as MODIFIED when only reordered');
                }
            ),
            { numRuns: 1000, verbose: true }
        );
    });

    test('Property 5: should handle message queue growth correctly (issue #291)', () => {
        fc.assert(
            fc.property(
                fc.uniqueArray(
                    fc.record({
                        type: fc.constantFrom('AppendEntries', 'RequestVote', 'Response'),
                        from: fc.integer({ min: 1, max: 5 }),
                        to: fc.integer({ min: 1, max: 5 })
                    }),
                    { minLength: 1, maxLength: 5, comparator: (a, b) => JSON.stringify(a) === JSON.stringify(b) }
                ),
                fc.uniqueArray(
                    fc.record({
                        type: fc.constantFrom('AppendEntries', 'RequestVote', 'Response'),
                        from: fc.integer({ min: 1, max: 5 }),
                        to: fc.integer({ min: 1, max: 5 })
                    }),
                    { minLength: 1, maxLength: 3, comparator: (a, b) => JSON.stringify(a) === JSON.stringify(b) }
                ),
                (baseMessages, additionalMessages) => {
                    // Ensure no overlap
                    const baseStrings = baseMessages.map(m => JSON.stringify(m));
                    const newMessages = additionalMessages.filter(m => !baseStrings.includes(JSON.stringify(m)));

                    if (newMessages.length === 0) {
                        // Skip if no new messages to add
                        return;
                    }

                    const oldSet = createMessageSet(baseMessages);
                    const newSet = createMessageSet([...baseMessages, ...newMessages]);

                    findChanges(oldSet, newSet);

                    // Existing messages should NOT be marked as added
                    baseMessages.forEach(msg => {
                        const foundItem = findItemByContent(newSet, JSON.stringify(msg));
                        assert.ok(foundItem, `Base message ${JSON.stringify(msg)} should exist in new set`);
                        assert.strictEqual(foundItem.changeType, Change.NOT_CHANGED,
                            `Existing message should be NOT_CHANGED, not ${foundItem.changeType}`);
                    });

                    // New messages should be marked as added
                    newMessages.forEach(msg => {
                        const foundItem = findItemByContent(newSet, JSON.stringify(msg));
                        assert.ok(foundItem, `New message ${JSON.stringify(msg)} should exist in new set`);
                        assert.strictEqual(foundItem.changeType, Change.ADDED,
                            `New message ${JSON.stringify(msg)} should be ADDED, not ${foundItem.changeType}`);
                    });
                }
            ),
            { numRuns: 1000, verbose: true }
        );
    });

    test('Property 6: should correctly mark set as modified when changes occur', () => {
        fc.assert(
            fc.property(
                fc.array(fc.string(), { minLength: 0, maxLength: 10 }),
                fc.array(fc.string(), { minLength: 0, maxLength: 10 }),
                (oldElements, newElements) => {
                    const oldSet = createTestSet(oldElements);
                    const newSet = createTestSet(newElements);

                    findChanges(oldSet, newSet);

                    const oldUnique = new Set(oldElements);
                    const newUnique = new Set(newElements);

                    const hasAdditions = [...newUnique].some(e => !oldUnique.has(e));
                    const hasDeletions = [...oldUnique].some(e => !newUnique.has(e));

                    if (hasAdditions || hasDeletions) {
                        assert.strictEqual(newSet.changeType, Change.MODIFIED,
                            'Set should be MODIFIED when elements are added or deleted');
                    } else {
                        assert.strictEqual(newSet.changeType, Change.NOT_CHANGED,
                            'Set should be NOT_CHANGED when no elements are added or deleted');
                    }
                }
            ),
            { numRuns: 1000, verbose: true }
        );
    });

    // Test with a specific case from issue #291
    test('Specific case: AppendEntries then RequestVote', () => {
        // Initial state: just AppendEntries
        const appendEntries = { type: 'AppendEntries', from: 1, to: 2 };
        const requestVote = { type: 'RequestVote', from: 1, to: 2 };

        const oldSet = createMessageSet([appendEntries]);
        const newSet = createMessageSet([appendEntries, requestVote]);

        findChanges(oldSet, newSet);

        // AppendEntries should be unchanged
        const appendEntriesItem = findItemByContent(newSet, JSON.stringify(appendEntries));
        assert.ok(appendEntriesItem, 'AppendEntries should exist in new set');
        assert.strictEqual(appendEntriesItem.changeType, Change.NOT_CHANGED,
            `AppendEntries should be NOT_CHANGED, but was ${appendEntriesItem.changeType}`);

        // RequestVote should be added
        const requestVoteItem = findItemByContent(newSet, JSON.stringify(requestVote));
        assert.ok(requestVoteItem, 'RequestVote should exist in new set');
        assert.strictEqual(requestVoteItem.changeType, Change.ADDED,
            `RequestVote should be ADDED, but was ${requestVoteItem.changeType}`);
    });
});

// Helper functions
function createTestSet(elements: string[]): SetValue {
    const items = elements.map((str, idx) => new Value(idx, str));
    return new SetValue('testSet', items);
}

interface Message {
    type: string;
    from: number;
    to: number;
}

function createMessageSet(messages: Message[]): SetValue {
    const items = messages.map((msg, idx) =>
        new Value(idx, JSON.stringify(msg))
    );
    return new SetValue('messages', items);
}

function findItemByContent(set: SetValue, content: string): Value | undefined {
    return set.items.find(item => item.str === content);
}