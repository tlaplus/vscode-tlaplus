import * as vscode from 'vscode';
import * as assert from 'assert';
import { beforeEach } from 'mocha';
import { TranspilerStdoutParser } from '../../../src/parsers/pluscal';
import { pathToUri } from '../../../src/common';
import { applyDCollection } from '../../../src/diagnostic';
import { getTlaDiagnostics } from './testUtils';

suite('PlusCal Transpiler Output Parser Test Suite', () => {
    beforeEach(() => {
        getTlaDiagnostics().clear();
    });

    test('No errors on successfull run', () => {
        const stdout = [
            'pcal.trans Version 1.9 of 10 July 2019',
            'Labels added.',
            'Parsing completed.',
            'Translation completed.',
            'New file /Users/bob/TLA/test.tla written.',
            'File /Users/bob/TLA/test.cfg already contains SPECIFICATION statement,',
            '    so new one not written.',
            'New file /Users/bob/TLA/test.cfg written.`'
        ].join('\n');
        assertOutput(stdout, '/Users/bob/TLA/test.tla', []);
    });

    test('Captures parsing error', () => {
        const stdout = [
            'pcal.trans Version 1.9 of 10 July 2019',
            '',
            'Unrecoverable error:',
            ' -- Expected "begin" but found "variabless"',
            ' line 8, column 1.',
            ''
        ].join('\n');
        assertOutput(stdout, '/Users/bob/TLA/err.tla', [
            new vscode.Diagnostic(
                new vscode.Range(7, 1, 7, 1),
                'Expected "begin" but found "variabless"',
                vscode.DiagnosticSeverity.Error)
        ]);
    });

    test('Captures unrecoverable errors with location', () => {
        const stdout = [
            'pcal.trans Version 1.9 of 10 July 2019',
            '',
            'Unrecoverable error:',
            '  -- Missing `;\' before line 13, column 9.',
            ''
        ].join('\n');
        assertOutput(stdout, '/Users/bob/TLA/err.tla', [
            new vscode.Diagnostic(
                new vscode.Range(12, 9, 12, 9),
                'Missing `;\' before',
                vscode.DiagnosticSeverity.Error)
        ]);
    });

    test('Ignore no-pluscal-code error', () => {
        const stdout = [
            'pcal.trans Version 1.9 of 10 July 2019',
            '',
            'Unrecoverable error:',
            ' -- Beginning of algorithm string --algorithm not found..',
            ''
        ].join('\n');
        assertOutput(stdout, '/Users/bob/TLA/err.tla', []);
    });

    test('Captures errors with blank message', () => {
        const stdout = [
            'pcal.trans Version 1.11 of 31 December 2020',
            'Parsing completed.',
            '',
            'Unrecoverable error:',
            ' -- ',
            'Process proc redefined at line 10, column 1.',
        ].join('\n');
        assertOutput(stdout, '/Users/bob/TLA/err.tla', [
            new vscode.Diagnostic(
                new vscode.Range(9, 1, 9, 1),
                'Process proc redefined',
                vscode.DiagnosticSeverity.Error)
        ]);
    });
});

function assertOutput(out: string, filePath: string, expected: vscode.Diagnostic[]) {
    const outLines = out.split('\n');
    const parser = new TranspilerStdoutParser(outLines, filePath);
    const dCol = parser.readAllSync();
    applyDCollection(dCol, getTlaDiagnostics());
    const diagnostics = getTlaDiagnostics().get(pathToUri(filePath));
    assert.deepEqual(diagnostics, expected);
}
