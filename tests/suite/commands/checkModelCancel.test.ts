import * as assert from 'assert';
import { SpecFiles } from '../../../src/model/check';
import { CheckSession } from '../../../src/services/checkService';

suite('CheckModel cancellation handling', () => {
    test('marks a session as cancelled when cancellation is requested before finish', () => {
        const session = new CheckSession(
            new SpecFiles('Example.tla', 'MCExample.cfg'),
            { showOptionsPrompt: false }
        );

        session.requestCancel();
        session.finish(undefined);

        assert.strictEqual(session.lifecycle, 'cancelled');
        assert.strictEqual(session.isActive, false);
    });
});
