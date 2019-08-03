import * as assert from 'assert';
import { beforeEach } from 'mocha';
import { SanyStdoutParser } from '../../../parsers/sany';
import { pathToUri } from '../../../common';
import { applyDCollection } from '../../../diagnostic';
import { Expectation, diagError, range, expectDiag, getTlaDiagnostics } from './testUtils';

const ROOT_PATH = '/Users/alice/TLA/foo.tla';
const ROOT_NAME = 'foo';

suite('SANY Output Parser Test Suite', () => {
    beforeEach(() => {
        getTlaDiagnostics().clear();
    });

    test('Clears errors on successfull run', () => {
        // This error must be removed after parsing
        getTlaDiagnostics().set(pathToUri(ROOT_PATH), [
            diagError(range(3, 5, 3, 12), 'Some existing error')
        ]);
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            'Parsing file /private/var/dependencies/TLC.tla',
            'Semantic processing of module TLC',
            `Semantic processing of module ${ROOT_NAME}`,
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, []),
            expectDiag('/private/var/dependencies/TLC.tla', []));
    });

    test('Captures semantic errors and fixes ranges in root module', () => {
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            'Parsing file /private/var/dependencies/TLC.tla',
            'Semantic processing of module TLC',
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Errors: 2',
            '',
            `line 7, col 3 to line 12, col 47 of module ${ROOT_NAME}`,
            '',
            'Something went wrong!',
            '',
            '',
            `line 14, col 6 to line 14, col 12 of module ${ROOT_NAME}`,
            '',
            "Unknown operator: `FooBar'.",
            ''
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(range(6, 2, 11, 47), 'Something went wrong!'),
                diagError(range(13, 5, 13, 12), "Unknown operator: `FooBar'.")
            ]),
            expectDiag('/private/var/dependencies/TLC.tla', []));
    });

    test('Captures semantic errors in non-root module', () => {
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            'Parsing file /private/var/dependencies/TLC.tla',
            'Parsing file /Users/alice/TLA/bar.tla',
            'Semantic processing of module TLC',
            'Semantic processing of module bar',
            'Semantic errors:',
            '*** Errors: 1',
            '',
            'line 17, col 5 to line 17, col 37 of module bar',
            '',
            'Bar has an error :(',
            ''
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, []),
            expectDiag('/private/var/dependencies/TLC.tla', []),
            expectDiag('/Users/alice/TLA/bar.tla', [
                diagError(range(16, 4, 16, 37), 'Bar has an error :(')
            ]));
    });

    test('Captures parsing errors in root module', () => {
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            '***Parse Error***',
            'Was expecting "==== or more Module body"',
            'Encountered "foobarbaz" at line 90, column 29 and token "\\"',
            '',
            'Residual stack trace follows:',
            'Module definition starting at line 1, column 1.',
            '',
            ''
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(range(89, 28, 89, 28), 'Was expecting "==== or more Module body"')
            ]));
    });

    test('Captures parsing errors in other modules', () => {
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            'Parsing file /Users/alice/TLA/bar.tla',
            '***Parse Error***',
            'Was expecting "==== or more Module body"',
            'Encountered "foobarbaz" at line 90, column 29 and token "\\"',
            '',
            'Residual stack trace follows:',
            'Module definition starting at line 1, column 1.',
            '',
            ''
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag('/Users/alice/TLA/bar.tla', [
                diagError(range(89, 28, 89, 28), 'Was expecting "==== or more Module body"')
            ]));
    });

    test('Captures lexical errors in root module', () => {
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            'Lexical error at line 102, column 15.  Encountered: "=" (61), after : "?"',
            '',
            'Fatal errors while parsing TLA+ spec in file sorting',
            '',
            'tla2sany.semantic.AbortException',
            '*** Abort messages: 1',
            `In module ${ROOT_NAME}`,
            ''
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(range(101, 14, 101, 14), 'Encountered: "=" (61), after : "?"')
            ]));
    });
});

function assertOutput(out: string, ...expected: Expectation[]) {
    const outLines = out.split('\n');
    const parser = new SanyStdoutParser(outLines);
    const dCol = parser.readAllSync();
    applyDCollection(dCol, getTlaDiagnostics());
    for (const exp of expected) {
        const actDiags = getTlaDiagnostics().get(pathToUri(exp.filePath));
        assert.deepEqual(actDiags, exp.diagnostics);
    }
}
