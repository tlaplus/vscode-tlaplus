import * as assert from 'assert';
import { ModelCheckResult, CheckState, CheckStatus, OutputLine, InitialStateStatItem } from '../../../src/model/check';
import { TlcModelCheckerStdoutParser } from '../../../src/parsers/tlc';
import moment = require('moment');
import { replaceExtension } from '../../../src/common';

const ROOT_PATH = '/Users/alice/TLA/foo.tla';

suite('TLC Output Parser Test Suite', () => {

    test('Captures Print/PrintT output', () => {
        const stdout = [
            '@!@!@STARTMSG 2262:0 @!@!@',
            'TLC2 Version X.Y of 1 Jan 2019 (rev: 0000000)',
            '@!@!@ENDMSG 2262 @!@!@',
            '@!@!@STARTMSG 2185:0 @!@!@',
            'Starting... (2019-01-01 01:02:03)',
            '@!@!@ENDMSG 2185 @!@!@',
            '@!@!@STARTMSG 2190:0 @!@!@',
            'Finished computing initial states: 5184 distinct states generated at 2019-01-01 00:02:03.',
            '@!@!@ENDMSG 2190 @!@!@',
            'Foo',
            'Bar',
            '@!@!@STARTMSG 999999:1 @!@!@',
            'Some message.',
            '@!@!@ENDMSG 999999 @!@!@',
            'Bar',
            'Baz',
            '@!@!@STARTMSG 2193:0 @!@!@',
            'Model checking completed. No error has been found.',
            'Estimates of the probability that TLC did not check all reachable states',
            'because two distinct states had the same fingerprint:',
            'calculated (optimistic):  val = 5.0E-13',
            '@!@!@ENDMSG 2193 @!@!@',
            '@!@!@STARTMSG 2186:0 @!@!@',
            'Finished in 2345ms at (2019-01-01 01:02:05)',
            '@!@!@ENDMSG 2186 @!@!@'
        ].join('\n');
        assertOutput(stdout, ROOT_PATH, new ModelCheckResult(
            'foo',
            CheckState.Success,
            CheckStatus.Finished,
            undefined,
            [ new InitialStateStatItem('00:00:00', 0, 5184, 5184, 5184) ],
            [], [], [], undefined,
            moment('2019-01-01 01:02:03'),
            moment('2019-01-01 01:02:05'),
            2345,
            0, undefined, [
                outLine('Foo'),
                outLine('Bar', 2),
                outLine('Baz')
            ]
        ));
    });
});

class CheckResultHolder {
    checkResult: ModelCheckResult = ModelCheckResult.EMPTY;
}

function assertOutput(out: string, tlaFilePath: string, expected: ModelCheckResult) {
    const outLines = out.split('\n');
    const crh = new CheckResultHolder();
    const outFilePath = replaceExtension(tlaFilePath, 'out');
    const parser = new TlcModelCheckerStdoutParser(outLines, tlaFilePath, outFilePath, (cr) => {
        crh.checkResult = cr;
    });
    parser.readAllSync();
    assertEquals(crh.checkResult, expected);
}

function assertEquals(actual: ModelCheckResult, expected: ModelCheckResult) {
    assert.equal(actual.state, expected.state);
    assert.equal(actual.status, expected.status);
    assert.equal(actual.processInfo, expected.processInfo);
    assert.equal(actual.startDateTimeStr, expected.startDateTimeStr);
    assert.equal(actual.endDateTimeStr, expected.endDateTimeStr);
    assert.equal(actual.duration, expected.duration);
    assert.deepEqual(actual.outputLines, expected.outputLines);
    assert.deepEqual(actual.initialStatesStat, expected.initialStatesStat);
    assert.deepEqual(actual.coverageStat, expected.coverageStat);
    assert.deepEqual(actual.errors, expected.errors);
    assert.deepEqual(actual.errorTrace, expected.errorTrace);
    assert.deepEqual(actual.sanyMessages, expected.sanyMessages);
}

function outLine(text: string, count?: number): OutputLine {
    const line = new OutputLine(text);
    if (count && count > 1) {
        for (let i = 0; i < count - 1; i++) {
            line.increment();
        }
    }
    return line;
}
