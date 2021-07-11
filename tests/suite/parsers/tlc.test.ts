import * as assert from 'assert';
import * as path from 'path';
import * as fs from 'fs';
import { DiagnosticSeverity } from 'vscode';
import { before } from 'mocha';
import { PassThrough } from 'stream';
import { ModelCheckResult, CheckState, CheckStatus, ModelCheckResultSource, Value,
    SpecFiles } from '../../../src/model/check';
import { TlcModelCheckerStdoutParser } from '../../../src/parsers/tlc';
import { CheckResultBuilder, pos, range, struct, v, set, message, sourceLink, traceItem } from '../shortcuts';

const TEST_SPEC_FILES = new SpecFiles('/Users/alice/TLA/foo.tla', '/Users/alice/TLA/foo.cfg');
const FIXTURES_PATH = path.resolve(__dirname, '../../../../tests/fixtures/parsers/tlc');

suite('TLC Output Parser Test Suite', () => {
    before(() => {
        Value.switchIdsOff();
    });

    test('Parses minimal PlusCal output', () => {
        return assertOutput('empty-calplus.out', TEST_SPEC_FILES,
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
                .addInitState('00:00:01', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .addCoverage('example', 'Lbl_1', '/Users/bob/example.tla', range(15, 0, 15, 5), 1, 1)
                .addCoverage('example', 'Terminating', '/Users/bob/example.tla', range(20, 0, 20, 11), 1, 0)
                .build()
        );
    });

    test('Captures Print/PrintT output', () => {
        return assertOutput('print-output.out', TEST_SPEC_FILES,
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

    test('Captures output from external modules that override stdout', () => {
        return assertOutput('override-stdout.out', TEST_SPEC_FILES,
            new CheckResultBuilder('foo', CheckState.Success, CheckStatus.Finished)
                .setStartDateTime('2019-01-01 01:02:03')
                .setEndDateTime('2019-01-01 01:02:05')
                .setDuration(2345)
                .addInitState('00:00:00', 0, 5184, 5184, 5184)
                .addOutLine('Line 1 from external module')
                .addOutLine('Line 2')
                .build()
        );
    });

    test('Respects severity levels', () => {
        return assertOutput('severity-levels.out', TEST_SPEC_FILES,
            new CheckResultBuilder('foo', CheckState.Error, CheckStatus.Finished)
                .setStartDateTime('2019-01-01 01:02:03')
                .setEndDateTime('2019-01-01 01:02:05')
                .setDuration(2345)
                .addInitState('00:00:00', 0, 5184, 5184, 5184)
                .addOutLine('Info message.')
                .addWarning([message('Warning message.')])
                .addError([message('Error message.')])
                .addError([message('TLC bug info.')])
                .build()
        );
    });

    test('Captures warnings', () => {
        return assertOutput('warning.out', TEST_SPEC_FILES,
            new CheckResultBuilder('warning.out', CheckState.Success, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/example.tla')
                .setStartDateTime('2019-08-17 00:11:08')
                .setEndDateTime('2019-08-17 00:11:09')
                .setDuration(886)
                .addWarning([
                    message('Please run the Java VM which executes TLC with a throughput optimized garbage collector'
                    + ' by passing the "-XX:+UseParallelGC" property.')
                ])
                .setProcessInfo(
                    'Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571'
                        + ' with 1 worker on 4 cores with 1820MB heap and 64MB offheap memory [pid: 91333]'
                        + ' (Mac OS X 10.14.5 x86_64, Amazon.com Inc. 11.0.3 x86_64, MSBDiskFPSet, DiskStateQueue).')
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:01', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .build()
        );
    });

    test('Reports failure when errors are present', () => {
        // The check state is Error despite the 2193 (TLC_SUCCESS) message.
        // It happens when the -continue option is used.
        return assertOutput('error-continue.out', TEST_SPEC_FILES,
            new CheckResultBuilder('error-continue.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/example.tla')
                .setStartDateTime('2019-08-17 00:11:08')
                .setEndDateTime('2019-08-17 00:11:09')
                .setDuration(886)
                .setProcessInfo(
                    'Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571'
                        + ' with 1 worker on 4 cores with 1820MB heap and 64MB offheap memory [pid: 91333]'
                        + ' (Mac OS X 10.14.5 x86_64, Amazon.com Inc. 11.0.3 x86_64, MSBDiskFPSet, DiskStateQueue).')
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:01', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .addError(
                    [message('Invariant FooInvariant is violated.')],
                    [
                        traceItem(1, 'Initial predicate', '', '', undefined, range(0, 0, 0, 0),
                            struct('', v('FooVar', '1..2'), v('BarVar', '-1'))
                        )
                    ]
                )
                .build()
        );
    });

    test('Captures SANY errors', () => {
        return assertOutput('sany-error.out', TEST_SPEC_FILES,
            new CheckResultBuilder('sany-error.out', CheckState.Error, CheckStatus.Finished)
                .setProcessInfo('Running breadth-first search Model-Checking with fp 86 and seed -5126315020031287108.')
                .addDColFilePath(TEST_SPEC_FILES.tlaFilePath)
                .setStartDateTime('2019-08-17 02:04:44')
                .setEndDateTime('2019-08-17 02:04:44')
                .setDuration(380)
                .addDColMessage(
                    TEST_SPEC_FILES.tlaFilePath,
                    range(4, 7, 4, 8),
                    "Unknown operator: `a'.",
                    DiagnosticSeverity.Error
                )
                .addError([message("Unknown operator: `a'.")])
                .addError([message('Parsing or semantic analysis failed.')])
                .build()
        );
    });

    test('Captures SANY warnings', () => {
        return assertOutput('sany-warning.out', TEST_SPEC_FILES,
            new CheckResultBuilder('sany-warning.out', CheckState.Error, CheckStatus.Finished)
                .setProcessInfo('Running breadth-first search Model-Checking with fp 86 and seed -5126315020031287108.')
                .addDColFilePath(TEST_SPEC_FILES.tlaFilePath)
                .setStartDateTime('2019-08-17 02:04:44')
                .setEndDateTime('2019-08-17 02:04:44')
                .setDuration(380)
                .addDColMessage(
                    TEST_SPEC_FILES.tlaFilePath,
                    range(4, 7, 4, 8),
                    "Multiple declarations of operator `a'.",
                    DiagnosticSeverity.Warning
                )
                .addWarning([message("Multiple declarations of operator `a'.")])
                .build()
        );
    });

    test('Parses error trace', () => {
        const specFiles = new SpecFiles('/Users/bob/error_trace.tla', '/Users/bob/error_trace.cfg');
        return assertOutput('error-trace.out', specFiles,
            new CheckResultBuilder('error-trace.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/error_trace.tla')
                .addDColFilePath('/private/var/folders/tla/Integers.tla')
                .addDColFilePath('/private/var/folders/tla/Naturals.tla')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 6 and seed -9020681683977717109.')
                .setStartDateTime('2019-08-17 02:37:50')
                .setEndDateTime('2019-08-17 02:37:51')
                .setDuration(1041)
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:01', 3, 4, 4, 1)
                .addCoverage('error_trace', 'Init', '/Users/bob/error_trace.tla', range(7, 0, 7, 4), 2, 2)
                .addCoverage('error_trace', 'SomeFunc', '/Users/bob/error_trace.tla', range(11, 0, 11, 11), 5, 3)
                .addError(
                    [message('Invariant FooInvariant is violated.')],
                    [
                        traceItem(1, 'Initial predicate', '', '', undefined, range(0, 0, 0, 0),
                            struct('', v('FooVar', '1..2'), v('BarVar', '-1'))
                        ),
                        traceItem(2,
                            'SomeFunc in error_trace', 'error_trace', 'SomeFunc',
                            '/Users/bob/error_trace.tla', range(12, 8, 14, 24),
                            struct('',
                                set('FooVar', v(1, '1')).setModified(),
                                v('BarVar', '1').setModified()
                            ).setModified()
                        ),
                        traceItem(3,
                            'SomeFunc in error_trace', 'error_trace', 'SomeFunc',
                            '/Users/bob/error_trace.tla', range(12, 8, 14, 24),
                            struct('',
                                set('FooVar',
                                    v(1, '4').setModified(),
                                    v(2, 'TRUE').setAdded()).setModified(),
                                v('BarVar', '40').setModified()
                            ).setModified()
                        )
                    ]
                )
                .build()
        );
    });

    test('Parses error trace with stuttering state', () => {
        const specFiles = new SpecFiles('/Users/bob/stuttering.tla', '/Users/bob/stuttering.cfg');
        return assertOutput('error-trace-stuttering.out', specFiles,
            new CheckResultBuilder('stuttering.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/stuttering.tla')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 6 and seed -9020681683977717109.')
                .setStartDateTime('2019-08-17 02:37:50')
                .setEndDateTime('2019-08-17 02:37:51')
                .setDuration(1041)
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:01', 3, 4, 4, 1)
                .addError(
                    [ message('Temporal properties were violated.')],
                    [
                        traceItem(1, 'Initial predicate', '', '', undefined, range(0, 0, 0, 0),
                            struct('', v('Foo', '1'))
                        ),
                        traceItem(2,
                            'Stuttering', '', '', undefined, range(0, 0, 0, 0), struct('')
                        )
                    ]
                )
                .build()
        );
    });

    test('Parses error trace with back-to-previous-state', () => {
        const specFiles = new SpecFiles('/Users/bob/back_to_state.tla', '/Users/bob/back_to_state.cfg');
        return assertOutput('error-trace-back-to-state.out', specFiles,
            new CheckResultBuilder('back_to_state.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/back_to_state.tla')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 6 and seed -9020681683977717109.')
                .setStartDateTime('2019-08-17 02:37:50')
                .setEndDateTime('2019-08-17 02:37:51')
                .setDuration(1041)
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:01', 3, 4, 4, 1)
                .addError(
                    [ message('Temporal properties were violated.')],
                    [
                        traceItem(1, 'Initial predicate', '', '', undefined, range(0, 0, 0, 0),
                            struct('', v('Foo', '1'))
                        ),
                        traceItem(2, 'Cycle in back_to_state', 'back_to_state', 'Cycle',
                            '/Users/bob/back_to_state.tla', range(41, 9, 47, 30),
                            struct('', v('Foo', '2').setModified()).setModified()
                        ),
                        traceItem(2, 'Back to state', 'back_to_state', 'Cycle',
                            '/Users/bob/back_to_state.tla', range(41, 9, 47, 30),
                            struct('')
                        )
                    ]
                )
                .build()
        );
    });

    test('Parses error trace with a single variable', () => {
        // Such variables has no `/\` at the beginning
        const specFiles = new SpecFiles('/Users/bob/error_trace.tla', '/Users/bob/error_trace.cfg');
        return assertOutput('error-trace-single.out', specFiles,
            new CheckResultBuilder('error-trace-single.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/error_trace.tla')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 6 and seed -9020681683977717109.')
                .setStartDateTime('2019-08-17 02:37:50')
                .setEndDateTime('2019-08-17 02:37:51')
                .setDuration(1041)
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:01', 3, 4, 4, 1)
                .addError(
                    [ message('Invariant FooInvariant is violated.')],
                    [
                        traceItem(1, 'Initial predicate', '', '', undefined, range(0, 0, 0, 0),
                            struct('', struct('Var', v('foo', '1'), v('bar', '2')))
                        )
                    ]
                )
                .build()
        );
    });

    test('Handles nested exception messages', () => {
        // Messages 1000 `TLC threw an unexpected exception...`
        // contains a nested message with details that must be combined with the outer one.
        return assertOutput('nested-exception-message.out', TEST_SPEC_FILES,
            new CheckResultBuilder('nested-exception-message.out', CheckState.Error, CheckStatus.Finished)
                .setProcessInfo('Running breadth-first search Model-Checking with fp 95 and seed -5827499341661814189.')
                .setEndDateTime('2019-08-18 21:16:19')
                .setDuration(262)
                .addError([
                    message('TLC threw an unexpected exception.'),
                    message('This was probably caused by an error in the spec or model.'),
                    message('See the User Output or TLC Console for clues to what happened.'),
                    message('The exception was a tlc2.tool.ConfigFileException'),
                    message(': '),
                    message('TLC found an error in the configuration file at line 6'),
                    message('It was expecting = or <-, but did not find it.')
                ])
                .build()
        );
    });

    test('Extracts links from error messages', () => {
        return assertOutput('error-message-links.out', TEST_SPEC_FILES,
            new CheckResultBuilder('error-message-links.out', CheckState.Error, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/error_message_links.tla')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 6 and seed -9020681683977717109.')
                .setStartDateTime('2019-08-17 02:37:50')
                .setEndDateTime('2019-08-17 02:37:51')
                .setDuration(1041)
                .addInitState('00:00:00', 0, 1, 1, 1)
                .addInitState('00:00:01', 3, 4, 4, 1)
                .addError([
                    message('The error occurred when TLC was evaluating the nested'),
                    message('expressions at the following positions:'),
                    message(
                        '0. ',
                        sourceLink(
                            'Line 38, column 10 to line 50, column 44 in error_message_links',
                            '/Users/bob/error_message_links.tla',
                            pos(37, 9)
                        )
                    ),
                    message(
                        '1. ',
                        sourceLink(
                            'Line 40, column 13 to line 42, column 24 in error_message_links',
                            '/Users/bob/error_message_links.tla',
                            pos(39, 12)
                        ),
                        '. It\'s a pity.'
                    )
                ])
                .build()
        );
    });

    test('Handles no-line-break message end', () => {
        // bla-bla-bla@!@!@ENDMSG 2193 @!@!@
        return assertOutput('no-line-break-end.out', TEST_SPEC_FILES,
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
                .addInitState('00:00:01', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .build()
        );
    });

    test('Handles no-line-break message switch', () => {
        // https://github.com/alygin/vscode-tlaplus/issues/47
        return assertOutput('no-line-break-switch.out', TEST_SPEC_FILES,
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
                .addInitState('00:00:01', 2, 3, 2, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .build()
        );
    });

    test('Rewrites initial state item with the same timestamp', () => {
        return assertOutput('state-timestamp-duplication.out', TEST_SPEC_FILES,
            new CheckResultBuilder('state-timestamp-duplication.out', CheckState.Success, CheckStatus.Finished)
                .addDColFilePath('/Users/bob/example.tla')
                .addDColFilePath('/private/var/folders/tla/T/TLC.tla')
                .setStartDateTime('2019-08-17 00:11:08')
                .setEndDateTime('2019-08-17 00:11:09')
                .setDuration(886)
                .setProcessInfo('Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571.')
                .addInitState('00:00:00', 0, 1, 1, 1)
                // .addInitState('00:00:01', 2, 3, 2, 0) <-- This one must be substituted for the following
                .addInitState('00:00:01', 2, 13, 12, 0)
                .addCoverage('example', 'Init', '/Users/bob/example.tla', range(13, 0, 13, 4), 1, 1)
                .addCoverage('example', 'Lbl_1', '/Users/bob/example.tla', range(15, 0, 15, 5), 1, 1)
                .addCoverage('example', 'Terminating', '/Users/bob/example.tla', range(20, 0, 20, 11), 1, 0)
                .build()
        );
    });

    test('Handles coverage info that contains location', () => {
        return assertOutput('coverage-with-location.out', TEST_SPEC_FILES,
            new CheckResultBuilder('coverage-with-location.out', CheckState.Success, CheckStatus.Finished)
                .addDColFilePath('/Users/alice/issue_209.tla')
                .addDColFilePath('/private/var/folders/tla/T/TLC.tla')
                .setStartDateTime('2021-07-10 11:49:12')
                .setEndDateTime('2021-07-10 11:49:13')
                .setDuration(1166)
                .setProcessInfo('Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571.')
                .addInitState('00:00:00', 2, 7, 3, 0)
                .addCoverage('issue_209', 'Init', '/Users/alice/issue_209.tla', range(4, 0, 4, 4), 1, 1)
                .addCoverage('issue_209', 'Next', '/Users/alice/issue_209.tla', range(5, 0, 5, 4), 6, 2)
                .build()
        );
    });

    test('Parses localized integers', () => {
        return assertOutput('localized-ints.out', TEST_SPEC_FILES,
            new CheckResultBuilder('localized-ints.out', CheckState.Stopped, CheckStatus.CheckingLiveness)
                .addDColFilePath('/Users/charlie/issue_229.tla')
                .setStartDateTime('2021-07-06 16:22:05')
                .setProcessInfo('Running breadth-first search Model-Checking with fp 22 and seed -5755320172003082571.')
                .addInitState('00:00:00', 0, 16, 16, 16)
                .addInitState('00:00:03', 6, 65577, 11342, 6463)
                .addInitState('00:01:11', 14, 3191033, 346966, 92794)
                .addInitState('00:02:31', 16, 6349139, 683798, 186242)
                .addCoverage('issue_229', 'Init', '/Users/charlie/issue_229.tla', range(36, 0, 36, 4), 16, 16)
                .addCoverage('issue_229', 'Next', '/Users/charlie/issue_229.tla', range(117, 0, 117, 4), 951429, 101618)
                .build()
        );
    });
});

class CheckResultHolder {
    checkResult: ModelCheckResult = ModelCheckResult.createEmpty(ModelCheckResultSource.OutFile);
}

function assertEquals(actual: ModelCheckResult, expected: ModelCheckResult) {
    assert.equal(actual.state, expected.state, "State doesn't match");
    assert.equal(actual.status, expected.status, "Status doesn't match");
    assert.equal(actual.processInfo, expected.processInfo, "Process info doesn't match");
    assert.equal(actual.startDateTimeStr, expected.startDateTimeStr, "Start date/time doesn't match");
    assert.equal(actual.endDateTimeStr, expected.endDateTimeStr, "End date/time doesn't match");
    assert.equal(actual.duration, expected.duration, "Duration doesn't match");
    assert.deepEqual(actual.outputLines, expected.outputLines, "Output lines don't match");
    assert.deepEqual(actual.initialStatesStat, expected.initialStatesStat, "Initial states statistics doesn't match");
    assert.deepEqual(actual.coverageStat, expected.coverageStat, "Coverage statistics doesn't match");
    assert.deepEqual(actual.sanyMessages, expected.sanyMessages, "SANY messages don't match");
    assert.deepEqual(actual.warnings, expected.warnings, "Warnings don't match");
    assert.deepEqual(actual.errors, expected.errors, "Erros don't match");
}

async function assertOutput(fileName: string, specFiles: SpecFiles, expected: ModelCheckResult): Promise<void> {
    const filePath = path.join(FIXTURES_PATH, fileName);
    const buffer = fs.readFileSync(filePath);
    const stream = new PassThrough();
    stream.end(buffer);
    const crh = new CheckResultHolder();
    const parser = new TlcModelCheckerStdoutParser(
        ModelCheckResultSource.OutFile,
        stream,
        specFiles,
        false,
        cr => { crh.checkResult = cr; }
    );
    return parser.readAll().then(() => assertEquals(crh.checkResult, expected));
}
