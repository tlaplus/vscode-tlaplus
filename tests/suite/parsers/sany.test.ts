import * as assert from 'assert';
import { beforeEach } from 'mocha';
import {
    SanyStdoutParser, hasTranslationChecksums, getDivergenceType
} from '../../../src/parsers/sany';
import { pathToUri } from '../../../src/common';
import { applyDCollection } from '../../../src/diagnostic';
import { Expectation, diagError, diagWarning, range, expectDiag, getTlaDiagnostics } from './testUtils';

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
            'Parsing file /private/var/dependencies/TLC.tla (jar:file:/bob/tla2tools.jar!/tla2sany/StdModules/TLC.tla)',
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
            'Parsing file /private/var/dependencies/TLC.tla (jar:file:/bob/tla2tools.jar!/tla2sany/StdModules/TLC.tla)',
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
                diagError(
                    range(89, 28, 89, 28),
                    'Was expecting "==== or more Module body"\n'
                        + 'Encountered "foobarbaz" at line 90, column 29 and token "\\"'
                )
            ]));
    });

    test('Captures parsing internal errors', () => {
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}.tla`,
            'java.lang.NullPointerException'
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(
                    range(0, 0, 0, 0),
                    `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}.tla\n`
                        + 'java.lang.NullPointerException'
                )
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
                diagError(
                    range(89, 28, 89, 28),
                    'Was expecting "==== or more Module body"\n'
                        + 'Encountered "foobarbaz" at line 90, column 29 and token "\\"'
                )
            ]));
    });

    test('Captures parsing errors with no text line', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            '***Parse Error***',
            'Encountered "Beginning of definition" at line 21, column 38 and token ":"',
            '',
            'Residual stack trace follows:',
            'ExtendableExpr starting at line 21, column 38.',
            'Definition starting at line 21, column 1.',
            '',
            'Fatal errors while parsing TLA+ spec in file operators',
            '',
            'tla2sany.semantic.AbortException',
            '*** Abort messages: 1',
            'In module operators',
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(
                    range(20, 37, 20, 37),
                    'Encountered "Beginning of definition" at line 21, column 38 and token ":"'
                )
            ]));
    });

    test('Captures lexical errors in root module', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            'Lexical error at line 102, column 15.  Encountered: "=" (61), after : "?"',
            '',
            `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}`,
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

    test('Captures module-not-found error', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            '',
            `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}`,
            '',
            'tla2sany.semantic.AbortException',
            '*** Abort messages: 1',
            '',
            'Unknown location',
            '',
            `Cannot find source file for module FooBar imported in module ${ROOT_NAME}.`
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(
                    range(0, 0, 0, 0),
                    `Cannot find source file for module FooBar imported in module ${ROOT_NAME}.`
                )
            ]));
    });

    test('Captures module-file-name-mismatch error', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            '',
            `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}`,
            '',
            'tla2sany.semantic.AbortException',
            '*** Abort messages: 1',
            '',
            'Unknown location',
            '',
            "File name 'Foo' does not match the name 'foo' of the top level module it contains."
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(
                    range(0, 0, 0, 0),
                    "File name 'Foo' does not match the name 'foo' of the top level module it contains."
                )
            ]));
    });

    test('Captures circular-dependencies error', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            '',
            `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}`,
            '',
            'tla2sany.semantic.AbortException',
            '*** Abort messages: 1',
            '',
            'Unknown location',
            '',
            'Circular dependency among .tla files; dependency cycle is:',
            '',
            '  foo.tla --> bar.tla --> foo.tla'
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(
                    range(0, 0, 0, 0),
                    'Circular dependency among .tla files; dependency cycle is:\n  foo.tla --> bar.tla --> foo.tla'
                )
            ]));
    });

    test('Captures indentation error', () => {
        const errLine = `Item at line 14, col 9 to line 14, col 9 of module ${ROOT_NAME}`
            + ' is not properly indented inside conjunction or  disjunction list item'
            + ` at line 11, col 9 to line 14, col 9 of module ${ROOT_NAME}`;
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            '',
            '***Parse Error***',
            errLine,
            'Residual stack trace follows:',
            'AND-OR Junction starting at line 9, column 9.',
            'ExtendableExpr starting at line 9, column 9.',
            'Definition starting at line 8, column 1.',
            'Module body starting at line 5, column 1.',
            `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}`,
            'tla2sany.semantic.AbortException',
            '*** Abort messages: 1',
            `In module ${ROOT_NAME}`,
            `Could not parse module ${ROOT_NAME} from file ${ROOT_NAME}.tla`,
            'SANY finished.'
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(range(13, 8, 13, 8), errLine)
            ]));
    });

    test ('Captures warnings', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `line 24, col 10 to line 24, col 25 of module ${ROOT_NAME}`,
            'Multiple declarations or definitions for symbol FooConst.'
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagWarning(
                    range(23, 9, 23, 25),
                    'Multiple declarations or definitions for symbol FooConst.'
                )
            ]));
    });

    test ('Captures multi-line messages', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `line 24, col 10 to line 24, col 25 of module ${ROOT_NAME}`,
            'Multiple declarations or definitions for symbol FooConst.',
            `This duplicates the one at line 3, col 10 to line 3, col 25 of module ${ROOT_NAME}.`,
            `line 31, col 8 to line 31, col 20 of module ${ROOT_NAME}`,
            'Multiple declarations or definitions for symbol BarConst.',
            `This duplicates the one at line 4, col 10 to line 4, col 25 of module ${ROOT_NAME}.`,
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagWarning(
                    range(23, 9, 23, 25),
                    'Multiple declarations or definitions for symbol FooConst.\n'
                        + `This duplicates the one at line 3, col 10 to line 3, col 25 of module ${ROOT_NAME}.`
                ),
                diagWarning(
                    range(30, 7, 30, 20),
                    'Multiple declarations or definitions for symbol BarConst.\n'
                        + `This duplicates the one at line 4, col 10 to line 4, col 25 of module ${ROOT_NAME}.`
                )
            ]));
    });

    test ('Captures both warnings and errors from one output', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Errors: 1',
            `line 13, col 1 to line 13, col 26 of module ${ROOT_NAME}`,
            'Operator FooBar already defined or declared.',
            '*** Warnings: 1',
            `line 13, col 1 to line 13, col 26 of module ${ROOT_NAME}`,
            'Multiple declarations or definitions for symbol FooBar.',
            `This duplicates the one at line 11, col 1 to line 11, col 26 of module ${ROOT_NAME}.`
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagError(
                    range(12, 0, 12, 26),
                    'Operator FooBar already defined or declared.'
                ),
                diagWarning(
                    range(12, 0, 12, 26),
                    'Multiple declarations or definitions for symbol FooBar.\n'
                        + `This duplicates the one at line 11, col 1 to line 11, col 26 of module ${ROOT_NAME}.`
                )
            ]));
    });

    test('Captures monolith spec error', () => {
        const stdout = [
            '',
            '****** SANY2 Version 2.1 created 24 February 2014',
            '',
            `Parsing file ${ROOT_PATH}`,
            'Parsing file /private/var/dependencies/TLC.tla',
            '***Parse Error***',
            'Encountered "tcolor" at line 8, column 9 and token "active"',
            '',
            `Fatal errors while parsing TLA+ spec in file ${ROOT_NAME}.tla`
        ].join('\n');
        assertOutputWithFileContents(
            stdout,
            (i) => '\n\n\n----- MODULE TLC ----' ,
            expectDiag(ROOT_PATH, [
                diagError(range(10, 8, 10, 8), 'Encountered "tcolor" at line 8, column 9 and token "active"')
            ]),
            expectDiag('/private/var/dependencies/TLC.tla', [
                diagError(range(0, 0, 0, 0), 'Fatal errors while parsing TLA+ spec in file foo.tla')
            ]));
    });

    test('Captures PlusCal algorithm divergence warning', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `In module ${ROOT_NAME}`,
            `The PlusCal algorithm in module ${ROOT_NAME} has changed since its last translation.`
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagWarning(
                    range(0, 0, 0, 0),
                    `In module ${ROOT_NAME}\n`
                        + `The PlusCal algorithm in module ${ROOT_NAME} has changed since its last translation.`
                )
            ]));
    });

    test('Captures TLA+ translation divergence warning', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `In module ${ROOT_NAME}`,
            `The TLA+ translation in module ${ROOT_NAME} has changed since its last translation.`
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagWarning(
                    range(0, 0, 0, 0),
                    `In module ${ROOT_NAME}\n`
                        + `The TLA+ translation in module ${ROOT_NAME} has changed since its last translation.`
                )
            ]));
    });

    test('Captures both PlusCal and TLA+ divergence warning', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `In module ${ROOT_NAME}`,
            `Both the PlusCal algorithm and its TLA+ translation in module ${ROOT_NAME}`
                + ' have changed since the last translation.'
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagWarning(
                    range(0, 0, 0, 0),
                    `In module ${ROOT_NAME}\n`
                        + `Both the PlusCal algorithm and its TLA+ translation in module ${ROOT_NAME}`
                        + ' have changed since the last translation.'
                )
            ]));
    });

    test('Captures divergence warning in syntax parsing format', () => {
        // This is the actual format SANY emits for divergence warnings
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            'Labels added.',
            `Warnings (1) during syntax parsing of ${ROOT_PATH}:`,
            `In module ${ROOT_NAME}`,
            `The TLA+ translation in module ${ROOT_NAME} has changed since its last translation.`,
            `Semantic processing of module ${ROOT_NAME}`,
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagWarning(
                    range(0, 0, 0, 0),
                    `In module ${ROOT_NAME}\n`
                        + `The TLA+ translation in module ${ROOT_NAME} has changed since its last translation.`
                )
            ]));
    });

    test('Handles divergence warning followed by regular warning', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 2',
            `In module ${ROOT_NAME}`,
            '',
            `The PlusCal algorithm in module ${ROOT_NAME} has changed since its last translation.`,
            '',
            '',
            `line 24, col 10 to line 24, col 25 of module ${ROOT_NAME}`,
            '',
            'Multiple declarations or definitions for symbol FooConst.'
        ].join('\n');
        assertOutput(
            stdout,
            expectDiag(ROOT_PATH, [
                diagWarning(
                    range(0, 0, 0, 0),
                    `In module ${ROOT_NAME}\n`
                        + `The PlusCal algorithm in module ${ROOT_NAME} has changed since its last translation.`
                ),
                diagWarning(
                    range(23, 9, 23, 25),
                    'Multiple declarations or definitions for symbol FooConst.'
                )
            ]));
    });

    test('getDivergenceType returns pcal for PlusCal-only divergence', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `In module ${ROOT_NAME}`,
            `The PlusCal algorithm in module ${ROOT_NAME} has changed since its last translation.`
        ].join('\n');
        const sanyData = assertOutputAndReturnData(stdout);
        assert.strictEqual(getDivergenceType(sanyData), 'pcal');
    });

    test('getDivergenceType returns tla for TLA+ divergence', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `In module ${ROOT_NAME}`,
            `The TLA+ translation in module ${ROOT_NAME} has changed since its last translation.`
        ].join('\n');
        const sanyData = assertOutputAndReturnData(stdout);
        assert.strictEqual(getDivergenceType(sanyData), 'tla');
    });

    test('getDivergenceType returns both for dual divergence', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `In module ${ROOT_NAME}`,
            `Both the PlusCal algorithm and its TLA+ translation in module ${ROOT_NAME}`
                + ' have changed since the last translation.'
        ].join('\n');
        const sanyData = assertOutputAndReturnData(stdout);
        assert.strictEqual(getDivergenceType(sanyData), 'both');
    });

    test('getDivergenceType returns none for non-divergence warnings', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
            'Semantic errors:',
            '*** Warnings: 1',
            `line 24, col 10 to line 24, col 25 of module ${ROOT_NAME}`,
            'Multiple declarations or definitions for symbol FooConst.'
        ].join('\n');
        const sanyData = assertOutputAndReturnData(stdout);
        assert.strictEqual(getDivergenceType(sanyData), 'none');
    });

    test('getDivergenceType returns tla in syntax parsing format', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            'Labels added.',
            `Warnings (1) during syntax parsing of ${ROOT_PATH}:`,
            `In module ${ROOT_NAME}`,
            `The TLA+ translation in module ${ROOT_NAME} has changed since its last translation.`,
            `Semantic processing of module ${ROOT_NAME}`,
        ].join('\n');
        const sanyData = assertOutputAndReturnData(stdout);
        assert.strictEqual(getDivergenceType(sanyData), 'tla');
    });

    test('getDivergenceType returns none when no warnings', () => {
        const stdout = [
            `Parsing file ${ROOT_PATH}`,
            `Semantic processing of module ${ROOT_NAME}`,
        ].join('\n');
        const sanyData = assertOutputAndReturnData(stdout);
        assert.strictEqual(getDivergenceType(sanyData), 'none');
    });

    test('hasTranslationChecksums returns true for checksum format', () => {
        const text = '\\* BEGIN TRANSLATION (chksum(pcal) = "abc" /\\ chksum(tla) = "def")\nVARIABLE pc\n';
        assert.strictEqual(hasTranslationChecksums(text), true);
    });

    test('hasTranslationChecksums returns false for plain BEGIN TRANSLATION', () => {
        const text = '\\* BEGIN TRANSLATION\nVARIABLE pc\n';
        assert.strictEqual(hasTranslationChecksums(text), false);
    });

    test('hasTranslationChecksums returns false for hash comment format', () => {
        const text = '\\* BEGIN TRANSLATION - the hash of the PCal code: PCal-abc\nVARIABLE pc\n';
        assert.strictEqual(hasTranslationChecksums(text), false);
    });

    test('hasTranslationChecksums returns false when no translation marker', () => {
        assert.strictEqual(hasTranslationChecksums('---- MODULE Foo ----\n====\n'), false);
    });

});

function assertOutput(out: string, ...expected: Expectation[]) {
    const outLines = out.split('\n');
    const parser = new SanyStdoutParser(outLines);
    const sanyData = parser.readAllSync();
    applyDCollection(sanyData.dCollection, getTlaDiagnostics());
    for (const exp of expected) {
        const actDiags = getTlaDiagnostics().get(pathToUri(exp.filePath));
        assert.deepEqual(actDiags, exp.diagnostics);
    }
}

function assertOutputAndReturnData(out: string) {
    const outLines = out.split('\n');
    const parser = new SanyStdoutParser(outLines);
    return parser.readAllSync();
}

function assertOutputWithFileContents(
    out: string, getFileContents : (filePath : string) => string, ...expected: Expectation[]) {
    const outLines = out.split('\n');
    const parser = new SanyStdoutParser(outLines);
    parser.getFileContents = getFileContents;
    const sanyData = parser.readAllSync();
    applyDCollection(sanyData.dCollection, getTlaDiagnostics());
    for (const exp of expected) {
        const actDiags = getTlaDiagnostics().get(pathToUri(exp.filePath));
        assert.deepEqual(actDiags, exp.diagnostics);
    }
}
