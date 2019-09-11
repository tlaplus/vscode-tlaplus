import * as vscode from 'vscode';
import * as assert from 'assert';
import { LANG_TLAPLUS } from '../../../src/common';
import { TlaDocumentSymbolsProvider, ROOT_SYMBOL_NAME } from '../../../src/symbols/tlaSymbols';
import { replaceDocContents } from '../document';
import { symModule, loc, range, symField, symFunc, symModRef, symBool } from '../shortcuts';

suite('TLA Symbols Provider Test Suite', () => {
    let doc: vscode.TextDocument;

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({ language: LANG_TLAPLUS });
    });

    suiteTeardown(async () => {
        await vscode.window.showTextDocument(doc, {preview: true, preserveFocus: false});
        return vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Handles empty document', () => {
        return assertSymbols(doc, [ '' ], []);
    });

    test('Finds module', () => {
        return assertSymbols(doc, [
            '---- MODULE foo ----'
        ], [
            symModule('foo', loc(doc.uri, range(0, 0, 0, 20)))
        ]);
    });

    test('Finds constant', () => {
        return assertSymbols(doc, [
            'Foo == 10'
        ], [
            symField('Foo', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 9)))
        ]);
    });

    test('Finds operator', () => {
        return assertSymbols(doc, [
            'Bar(foo) == foo + 10'
        ], [
            symFunc('Bar', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 20)))
        ]);
    });

    test('Finds function', () => {
        return assertSymbols(doc, [
            'Baz[foo \\in 1..3] == foo + 11'
        ], [
            symFunc('Baz', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 29)))
        ]);
    });

    test('Finds module reference', () => {
        return assertSymbols(doc, [
            'FooMod == INSTANCE foo'
        ], [
            symModRef('FooMod', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 22)))
        ]);
    });

    test('Finds theorem', () => {
        return assertSymbols(doc, [
            'THEOREM LifeIsGood == \\A day \\in life: IsHappy(day)'
        ], [
            symBool('LifeIsGood', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 51)))
        ]);
    });

    test('Finds axiom', () => {
        return assertSymbols(doc, [
            'AXIOM Truth == TRUE'
        ], [
            symBool('Truth', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 19)))
        ]);
    });

    test('Captures symbol with no value', () => {
        return assertSymbols(doc, [
            'Multiline =='
        ], [
            symField('Multiline', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 12)))
        ]);
    });

    test('Doesn\'t capture PlusCal definitions', () => {
        return assertSymbols(doc, [ 'v1 = 4' ], []);
    });

    test('Puts simbols into module', () => {
        return assertSymbols(doc, [
            '---- MODULE bar ----',
            'FOO == 17',
            'BAZ(x) == x'
        ], [
            symModule('bar', loc(doc.uri, range(0, 0, 2, 11))),
            symField('FOO', 'bar', loc(doc.uri, range(1, 0, 1, 9))),
            symFunc('BAZ', 'bar', loc(doc.uri, range(2, 0, 2, 11))),
        ]);
    });

    test('Ignores leading whitespaces', () => {
        return assertSymbols(doc, [
            ' \t  Zero == 0'
        ], [
            symField('Zero', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 13)))
        ]);
    });

    test('Captures non-alphabetic symbols', () => {
        return assertSymbols(doc, [
            'This_is_3 == 3'
        ], [
            symField('This_is_3', ROOT_SYMBOL_NAME, loc(doc.uri, range(0, 0, 0, 14)))
        ]);
    });

    test('Captures duplicates', () => {
        return assertSymbols(doc, [
            'LET',
            '    One == 1',
            'IN One',
            'LET',
            '    One == 1',
            'IN Handle(One)'
        ], [
            symField('One', ROOT_SYMBOL_NAME, loc(doc.uri, range(1, 0, 1, 12))),
            symField('One', ROOT_SYMBOL_NAME, loc(doc.uri, range(4, 0, 4, 12)))
        ]);
    });

    test('Doesn\'t capture commented out lines', () => {
        return assertSymbols(doc, [
            '\\* Hello == "world"'
        ], []);
    });

    test('CAN IMPROVE: Captures symbols in block comments', () => {
        return assertSymbols(doc, [
            '(*',
            'Apply(op(_)) ==',
            '*)'
        ], [
            // Actually, we don't want to capture this
            symFunc('Apply', ROOT_SYMBOL_NAME, loc(doc.uri, range(1, 0, 1, 15)))
        ]);
    });

    test('CAN IMPROVE: Captures symbols in PlusCal define block', () => {
        return assertSymbols(doc, [
            '(* --algorithm foo',
            'define',
            '  Baz == 39',
            'end define',
            'begin',
            '  skip;',
            'end algorithm; *)'
        ], [
            // Actually, we don't want to capture this
            symField('Baz', ROOT_SYMBOL_NAME, loc(doc.uri, range(2, 0, 2, 11)))
        ]);
    });
});

async function assertSymbols(
    doc: vscode.TextDocument,
    docLines: string[],
    expectSymbols: object[]
): Promise<void> {
    const symbolsProvider = new TlaDocumentSymbolsProvider();
    await replaceDocContents(doc, docLines.join('\n'));
    const tokenSrc = new vscode.CancellationTokenSource();
    const symbols = symbolsProvider.provideDocumentSymbols(doc, tokenSrc.token);
    assert.deepEqual(symbols, expectSymbols);
    return undefined;
}
