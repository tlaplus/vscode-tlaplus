import * as assert from 'assert';
import { SpecFiles } from '../../../src/model/check';
import { CheckSession, SessionRegistry } from '../../../src/services/checkService';

suite('CheckService sessions', () => {
    test('SessionRegistry keeps multiple sessions and latest active/completed state', () => {
        const registry = new SessionRegistry();
        const sessionOne = new CheckSession(new SpecFiles('SpecA.tla', 'MCA.cfg'), { showOptionsPrompt: false });
        const sessionTwo = new CheckSession(new SpecFiles('SpecB.tla', 'MCB.cfg'), { showOptionsPrompt: false });

        registry.add(sessionOne);
        registry.add(sessionTwo);

        assert.strictEqual(registry.active().length, 2);
        assert.strictEqual(registry.lastSpecFiles(), sessionTwo.specFiles);
        assert.ok(registry.active().includes(sessionOne));
        assert.ok(registry.active().includes(sessionTwo));

        sessionOne.finish(undefined);

        assert.strictEqual(registry.latestCompleted(), sessionOne);
        assert.strictEqual(registry.latestActive(), sessionTwo);
    });

    test('Completed session snapshot remains available while another session is active', () => {
        const registry = new SessionRegistry();
        const completed = new CheckSession(new SpecFiles('SpecA.tla', 'MCA.cfg'), { showOptionsPrompt: false });
        const active = new CheckSession(new SpecFiles('SpecB.tla', 'MCB.cfg'), { showOptionsPrompt: false });

        registry.add(completed);
        completed.finish(undefined);
        registry.add(active);

        assert.strictEqual(registry.latestCompleted(), completed);
        assert.strictEqual(registry.latestActive(), active);
        assert.strictEqual(registry.active().length, 1);
    });
});
