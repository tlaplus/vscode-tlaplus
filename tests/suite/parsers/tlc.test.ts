import * as assert from 'assert';
import * as path from 'path';
import * as fs from 'fs';
import { PassThrough } from 'stream';
import { ModelCheckResult, CheckState, CheckStatus } from '../../../src/model/check';
import { TlcModelCheckerStdoutParser } from '../../../src/parsers/tlc';
import { replaceExtension } from '../../../src/common';
import { range, CheckResultBuilder } from '../shortcuts';

const ROOT_PATH = '/Users/alice/TLA/foo.tla';
const FIXTURES_PATH = path.resolve(__dirname, '../../../../tests/fixtures/parsers/tlc');

suite('TLC Output Parser Test Suite', () => {

    test('Parses minimal PlusCal output', () => {
        return assertOutput('empty-calplus.out', ROOT_PATH,
            new CheckResultBuilder('empty-calplus.out', CheckState.Success, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/example.tla')
                .addDColFilePath('/private/var/folders/tla/T/TLC.tla')
                .addDColFilePath('/private/var/folders/tla/T/Naturals.tla')
                .addDColFilePath('/private/var/folders/tla/T/Sequences.tla')
                .addDColFilePath('/private/var/folders/tla/T/FiniteSets.tla')
                .setStartDateTime('2019-08-17 00:11:08')
                .setEndDateTime('2019-08-17 00:11:09')
                .setDuration(886)
                .setProcessInfo(
                    'Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571'
                        + ' with 1 worker on 4 cores with 1820MB heap and 64MB offheap memory [pid: 91333]'
                        + ' (Mac OS X 10.14.5 x86_64, Amazon.com Inc. 11.0.3 x86_64, MSBDiskFPSet, DiskStateQueue).')
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:00', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .addCoverage('example', 'Lbl_1', '/Users/bob/example.tla', range(15, 0, 15, 5), 1, 1)
                .addCoverage('example', 'Terminating', '/Users/bob/example.tla', range(20, 0, 20, 11), 0, 1)
                .build()
            );
    });

    test('Captures Print/PrintT output', () => {
        return assertOutput('print-output.out', ROOT_PATH,
            new CheckResultBuilder('foo', CheckState.Success, CheckStatus.Finished)
                .setStartDateTime('2019-01-01 01:02:03')
                .setEndDateTime('2019-01-01 01:02:05')
                .setDuration(2345)
                .addInitState('00:00:00', 0, 5184, 5184, 5184)
                .addOutLine('Foo')
                .addOutLine('Bar', 2)
                .addOutLine('Baz')
                .build()
        );
    });
});

class CheckResultHolder {
    checkResult: ModelCheckResult = ModelCheckResult.EMPTY;
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

async function assertOutput(fileName: string, tlaFilePath: string, expected: ModelCheckResult): Promise<void> {
    const filePath = path.join(FIXTURES_PATH, fileName);
    const buffer = fs.readFileSync(filePath);
    const stream = new PassThrough();
    stream.end(buffer);
    const crh = new CheckResultHolder();
    const outFilePath = replaceExtension(tlaFilePath, 'out');
    const parser = new TlcModelCheckerStdoutParser(stream, tlaFilePath, outFilePath, (cr) => {
        crh.checkResult = cr;
    });
    return parser.readAll().then(() => assertEquals(crh.checkResult, expected));
}
