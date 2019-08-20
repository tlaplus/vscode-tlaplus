import * as assert from 'assert';
import * as path from 'path';
import * as fs from 'fs';
import { PassThrough } from 'stream';
import { ModelCheckResult, CheckState, CheckStatus, Change } from '../../../src/model/check';
import { TlcModelCheckerStdoutParser } from '../../../src/parsers/tlc';
import { replaceExtension } from '../../../src/common';
import { CheckResultBuilder, range, struct, v, set } from '../shortcuts';

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

    test('Captures warnings', () => {
        return assertOutput('warning.out', ROOT_PATH,
            new CheckResultBuilder('warning.out', CheckState.Success, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/example.tla')
                .setStartDateTime('2019-08-17 00:11:08')
                .setEndDateTime('2019-08-17 00:11:09')
                .setDuration(886)
                .addWarning([
                    'Please run the Java VM which executes TLC with a throughput optimized garbage collector'
                    + ' by passing the "-XX:+UseParallelGC" property.'
                ])
                .setProcessInfo(
                    'Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571'
                        + ' with 1 worker on 4 cores with 1820MB heap and 64MB offheap memory [pid: 91333]'
                        + ' (Mac OS X 10.14.5 x86_64, Amazon.com Inc. 11.0.3 x86_64, MSBDiskFPSet, DiskStateQueue).')
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:00', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .build()
            );
    });

    test('Captures SANY errors', () => {
        return assertOutput('sany-error.out', ROOT_PATH,
            new CheckResultBuilder('sany-error.out', CheckState.Error, CheckStatus.Finished)
                .setProcessInfo('Running breadth-first search Model-Checking with fp 86 and seed -5126315020031287108.')
                .addDColFilePath(ROOT_PATH)
                .setStartDateTime('2019-08-17 02:04:44')
                .setEndDateTime('2019-08-17 02:04:44')
                .setDuration(380)
                .addDColMessage(ROOT_PATH, range(4, 7, 4, 8), "Unknown operator: `a'.")
                .addError(["Unknown operator: `a'."])
                .addError(['Parsing or semantic analysis failed.'])
                .build()
        );
    });

    test('Parses error trace', () => {
        return assertOutput('error-trace.out', '/Users/bob/error_trace.tla',
            new CheckResultBuilder('error-trace.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/error_trace.tla')
                .addDColFilePath('/private/var/folders/tla/Integers.tla')
                .addDColFilePath('/private/var/folders/tla/Naturals.tla')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 6 and seed -9020681683977717109.')
                .setStartDateTime('2019-08-17 02:37:50')
                .setEndDateTime('2019-08-17 02:37:51')
                .setDuration(1041)
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:00', 3, 4, 4, 1)
                .addCoverage('error_trace', 'Init', '/Users/bob/error_trace.tla', range(7, 0, 7, 4), 2, 2)
                .addCoverage('error_trace', 'SomeFunc', '/Users/bob/error_trace.tla', range(11, 0, 11, 11), 3, 5)
                .addError(['Invariant FooInvariant is violated.'])
                .addTraceItem('Initial predicate', '', '', undefined, range(0, 0, 0, 0),
                    struct('', v('FooVar', '1..2'), v('BarVar', '-1'))
                )
                .addTraceItem(
                    'SomeFunc in error_trace', 'error_trace', 'SomeFunc',
                    '/Users/bob/error_trace.tla', range(12, 8, 14, 24),
                    struct('',
                        set('FooVar', v(1, '1')).setModified(),
                        v('BarVar', '1').setModified()
                    ).setModified()
                )
                .addTraceItem(
                    'SomeFunc in error_trace', 'error_trace', 'SomeFunc',
                    '/Users/bob/error_trace.tla', range(12, 8, 14, 24),
                    struct('',
                        set('FooVar',
                            v(1, '4').setModified(),
                            v(2, 'TRUE').setAdded()).setModified(),
                        v('BarVar', '40').setModified()
                    ).setModified()
                )
                .build()
        );
    });

    test('Parses error trace with a single variable', () => {
        // Such variables has no `/\` at the beginning
        return assertOutput('error-trace-single.out', '/Users/bob/error_trace.tla',
            new CheckResultBuilder('error-trace-single.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/error_trace.tla')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 6 and seed -9020681683977717109.')
                .setStartDateTime('2019-08-17 02:37:50')
                .setEndDateTime('2019-08-17 02:37:51')
                .setDuration(1041)
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:00', 3, 4, 4, 1)
                .addError(['Invariant FooInvariant is violated.'])
                .addTraceItem('Initial predicate', '', '', undefined, range(0, 0, 0, 0),
                    struct('', struct('Var', v('foo', '1'), v('bar', '2')))
                )
                .build()
        );
    });

    test('Handles nested exception messages', () => {
        // Messages 1000 `TLC threw an unexpected exception...`
        // contains a nested message with details that must be combined with the outer one.
        return assertOutput('nested-exception-message.out', ROOT_PATH,
            new CheckResultBuilder('nested-exception-message.out', CheckState.Error, CheckStatus.Finished)
                .setProcessInfo('Running breadth-first search Model-Checking with fp 95 and seed -5827499341661814189.')
                .setEndDateTime('2019-08-18 21:16:19')
                .setDuration(262)
                .addError([
                    'TLC threw an unexpected exception.',
                    'This was probably caused by an error in the spec or model.',
                    'See the User Output or TLC Console for clues to what happened.',
                    'The exception was a tlc2.tool.ConfigFileException',
                    ': ',
                    'TLC found an error in the configuration file at line 6',
                    'It was expecting = or <-, but did not find it.'
                ])
                .build()
            );
    });

    test('Handles no-line-break message end', () => {
        // bla-bla-bla@!@!@ENDMSG 2193 @!@!@
        return assertOutput('no-line-break-end.out', ROOT_PATH,
            new CheckResultBuilder('no-line-break-end.out', CheckState.Success, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/example.tla')
                .setStartDateTime('2019-08-17 00:12:01')
                .setEndDateTime('2019-08-17 00:12:02')
                .setDuration(400)
                .setProcessInfo(
                    'Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571'
                        + ' with 1 worker on 4 cores with 1820MB heap and 64MB offheap memory [pid: 91333]'
                        + ' (Mac OS X 10.14.5 x86_64, Amazon.com Inc. 11.0.3 x86_64, MSBDiskFPSet, DiskStateQueue).')
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:00', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .build()
            );
    });

    test('Handles no-line-break message switch', () => {
        // https://github.com/alygin/vscode-tlaplus/issues/47
        return assertOutput('no-line-break-switch.out', ROOT_PATH,
            new CheckResultBuilder('no-line-break-switch.out', CheckState.Success, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/example.tla')
                .setStartDateTime('2019-08-17 00:12:01')
                .setEndDateTime('2019-08-17 00:12:02')
                .setDuration(400)
                .setProcessInfo(
                    'Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571'
                        + ' with 1 worker on 4 cores with 1820MB heap and 64MB offheap memory [pid: 91333]'
                        + ' (Mac OS X 10.14.5 x86_64, Amazon.com Inc. 11.0.3 x86_64, MSBDiskFPSet, DiskStateQueue).')
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:00', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
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
    assert.deepEqual(actual.sanyMessages, expected.sanyMessages);
    assert.deepEqual(actual.warnings, expected.warnings);
    assert.deepEqual(actual.errors, expected.errors);
    assert.deepEqual(actual.errorTrace, expected.errorTrace);
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
