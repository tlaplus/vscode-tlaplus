import * as assert from 'assert';
import { CheckStatus, getStatusName } from '../../../model/check';

suite('Check Model Test Suite', () => {

    test('Throws when trying to get undefined status name', () => {
        const nonexistentStatus = Object.values(CheckStatus).length + 100;
        assert.throws(() => getStatusName(nonexistentStatus), Error);
    });

    test('All check statuses have names', () => {
        const statuses: CheckStatus[] = Object.values(CheckStatus).filter(x => typeof x === 'number');
        statuses.forEach(s => getStatusName(s));
    });
});
