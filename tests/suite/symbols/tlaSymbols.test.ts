import * as vscode from 'vscode';
import * as assert from 'assert';
import { LANG_TLAPLUS } from '../../../src/common';
import { TlaDocumentSymbolsProvider, ROOT_CONTAINER_NAME,
    PLUS_CAL_DEFAULT_NAME } from '../../../src/symbols/tlaSymbols';
import { replaceDocContents } from '../document';
import { symModule, loc, range, symField, symFunc, symModRef, symBool, pos, symPlusCal, symConst,
    symVar } from '../shortcuts';
import { TlaDocumentInfos } from '../../../src/model/documentInfo';

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
            '---- MODULE foo ----',
            '(* body *)',
            '===='
        ], [
            symModule('foo', loc(doc.uri, range(0, 0, 2, 4)))
        ]);
    });

    test('Finds items in CONSTANT', () => {
        return assertSymbols(doc, [
            'CONSTANT Foo, Bar'
        ], [
            symConst('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 9))),
            symConst('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 14)))
        ]);
    });

    test('Finds items in CONSTANTS', () => {
        return assertSymbols(doc, [
            'CONSTANTS Foo, Bar'
        ], [
            symConst('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 10))),
            symConst('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 15)))
        ]);
    });

    test('Finds items in VARIABLE', () => {
        return assertSymbols(doc, [
            'VARIABLE Foo, Bar'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 9))),
            symVar('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 14)))
        ]);
    });

    test('Finds items in VARIABLES', () => {
        return assertSymbols(doc, [
            'VARIABLES Foo, Bar'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 10))),
            symVar('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 15)))
        ]);
    });

    test('Finds items in multiline list', () => {
        return assertSymbols(doc, [
            'CONSTANTS Foo, Bar,',
            '    Baz,',
            '    BarBaz, FooBaz'
        ], [
            symConst('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 10))),
            symConst('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 15))),
            symConst('Baz', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 4))),
            symConst('BarBaz', ROOT_CONTAINER_NAME, loc(doc.uri, pos(2, 4))),
            symConst('FooBaz', ROOT_CONTAINER_NAME, loc(doc.uri, pos(2, 12))),
        ]);
    });

    test('Handles items list with no items on the first line', () => {
        return assertSymbols(doc, [
            'CONSTANTS',
            '  Foo'
        ], [
            symConst('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 2)))
        ]);
    });

    test('Handles spaces in items lists corectly', () => {
        return assertSymbols(doc, [
            'CONSTANTS   Foo  ,, Bar,Baz  ,',
            '   FooBar  '
        ], [
            symConst('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 12))),
            symConst('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 20))),
            symConst('Baz', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 24))),
            symConst('FooBar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 3)))
        ]);
    });

    test('Finishes items list when another block starts', () => {
        return assertSymbols(doc, [
            'CONSTANT Foo',
            'VARIABLE Bar',
            'Baz == 1'
        ], [
            symConst('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 9))),
            symVar('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 9))),
            symField('Baz', ROOT_CONTAINER_NAME, loc(doc.uri, range(2, 0, 2, 8)))
        ]);
    });

    test('Doesn\'t break items list on empty line', () => {
        return assertSymbols(doc, [
            'VARIABLES Foo,',
            '',
            '   Bar'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 10))),
            symVar('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(2, 3)))
        ]);
    });

    test('Handles line comments inside items list', () => {
        return assertSymbols(doc, [
            'VARIABLES',
            '   Foo,   \\* this is foo',
            '          \\* nothing interesting here',
            '   Bar,   \\* this is bar',
            '   Baz'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 3))),
            symVar('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(3, 3))),
            symVar('Baz', ROOT_CONTAINER_NAME, loc(doc.uri, pos(4, 3)))
        ]);
    });

    test('Handles on-line block comments inside items list', () => {
        return assertSymbols(doc, [
            'VARIABLES',
            '   Foo,   (* this is foo *)',
            '          (* nothing interesting here *)',
            '   Bar,   (* this is bar *)',
            '   Baz'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 3))),
            symVar('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, pos(3, 3))),
            symVar('Baz', ROOT_CONTAINER_NAME, loc(doc.uri, pos(4, 3)))
        ]);
    });

    test('Finds last list item with a line comment', () => {
        return assertSymbols(doc, [
            'VARIABLE',
            '  Foo   \\* some comment'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 2)))
        ]);
    });

    test('Finds last list item with a block comment', () => {
        return assertSymbols(doc, [
            'VARIABLE',
            '  Foo   (* some comment *)'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(1, 2)))
        ]);
    });

    test('Breaks items list after an item with no comma', () => {
        return assertSymbols(doc, [
            'VARIABLES Foo',
            'Something'
        ], [
            symVar('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 10)))
        ]);
    });

    test('Finds simple def', () => {
        return assertSymbols(doc, [
            'Foo == 10'
        ], [
            symField('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 0, 9)))
        ]);
    });

    test('Finds simple def block', () => {
        return assertSymbols(doc, [
            'Foo == 10',
            '       /\\ 20',
            '       /\\ 30',
        ], [
            symField('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 2, 12)))
        ]);
    });

    test('Finds local definitions in multi-level def block', () => {
        return assertSymbols(doc, [
            'Foo ==',
            '  LET bar == Something',
            '      baz == OtherThing',
            '      IN',
            '      /\\ bar /= 0',
            '      /\\ LET tau == FooBarBaz',
            '(****)'
        ], [
            symField('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 5, 29))),
            symVar('bar', 'Foo', loc(doc.uri, pos(1, 6))),
            symVar('baz', 'Foo', loc(doc.uri, pos(2, 6))),
            symVar('tau', 'Foo', loc(doc.uri, pos(5, 13))),
        ]);
    });

    test('Finds local definitions in indented multi-level def block', () => {
        return assertSymbols(doc, [
            '  Foo ==',
            '    LET bar == Something',
            '  Bar ==',
            '    LET baz == OtherThing',
            '        /\\ LET tau == FooBarBaz',
            '  (****)'
        ], [
            symField('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 2, 1, 24))),
            symVar('bar', 'Foo', loc(doc.uri, pos(1, 8))),
            symField('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, range(2, 2, 4, 31))),
            symVar('baz', 'Bar', loc(doc.uri, pos(3, 8))),
            symVar('tau', 'Bar', loc(doc.uri, pos(4, 15))),
        ]);
    });

    test('Ignores empty lines in def blocks', () => {
        return assertSymbols(doc, [
            'Foo == 10',
            '       /\\ 20',
            '',
            'Bar == 20'
        ], [
            symField('Foo', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 1, 12))),
            symField('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, range(3, 0, 3, 9))),
        ]);
    });

    test('Finds operator', () => {
        return assertSymbols(doc, [
            'Bar(foo) == foo + 10'
        ], [
            symFunc('Bar', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 0, 20)))
        ]);
    });

    test('Finds function', () => {
        return assertSymbols(doc, [
            'Baz[foo \\in 1..3] == foo + 11'
        ], [
            symFunc('Baz', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 0, 29)))
        ]);
    });

    test('Finds module reference', () => {
        return assertSymbols(doc, [
            'FooMod == INSTANCE foo'
        ], [
            symModRef('FooMod', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 0, 22)))
        ]);
    });

    test('Finds theorem', () => {
        return assertSymbols(doc, [
            'THEOREM LifeIsGood == \\A day \\in life: IsHappy(day)'
        ], [
            symBool('LifeIsGood', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 0)))
        ]);
    });

    test('Ignores theorems with =>', () => {
        return assertSymbols(doc, [ 'THEOREM TwoRabbits => ThreeRabbits' ], []);
    });

    test('Finds axiom', () => {
        return assertSymbols(doc, [
            'AXIOM Truth == TRUE'
        ], [
            symBool('Truth', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 0)))
        ]);
    });

    test('Finds lemma', () => {
        return assertSymbols(doc, [
            'LEMMA LemmA == TRUE'
        ], [
            symBool('LemmA', ROOT_CONTAINER_NAME, loc(doc.uri, pos(0, 0)))
        ]);
    });

    test('Captures symbol with no value', () => {
        return assertSymbols(doc, [
            'Multiline =='
        ], [
            symField('Multiline', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 0, 12)))
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
            symField('Zero', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 4, 0, 13)))
        ]);
    });

    test('Captures non-alphabetic symbols', () => {
        return assertSymbols(doc, [
            'This_is_3 == 3'
        ], [
            symField('This_is_3', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 0, 14)))
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
            symField('One', ROOT_CONTAINER_NAME, loc(doc.uri, range(1, 4, 1, 12))),
            symField('One', ROOT_CONTAINER_NAME, loc(doc.uri, range(4, 4, 4, 12)))
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
            symFunc('Apply', ROOT_CONTAINER_NAME, loc(doc.uri, range(1, 0, 1, 15)))
        ]);
    });

    test('Finds PlusCal algorithm', () => {
        return assertSymbols(doc, [
            'A == 10',
            '(* --algorithm foo',
            'begin',
            '  skip;',
            'end algorithm; *)',
            'B == 20'
        ], [
            symField('A', ROOT_CONTAINER_NAME, loc(doc.uri, range(0, 0, 0, 7))),
            symField('B', ROOT_CONTAINER_NAME, loc(doc.uri, range(5, 0, 5, 7))),
            // PlusCal symbols always come last
            symPlusCal('foo', loc(doc.uri, range(1, 0, 4, 17)))
        ]);
    });

    test('Finds symbols in PlusCal algorithm', () => {
        return assertSymbols(doc, [
            '(* --algorithm bar',
            'define',
            '  Baz == 39',
            'end define',
            'begin',
            '  skip;',
            'end algorithm; *)',
            'Baz == 39'
        ], [
            symField('Baz', ROOT_CONTAINER_NAME, loc(doc.uri, range(7, 0, 7, 9))),
            // PlusCal symbols always come last
            symPlusCal('bar', loc(doc.uri, range(0, 0, 6, 17))),
            symField('Baz', 'bar', loc(doc.uri, range(2, 2, 2, 11)))
        ]);
    });

    test('Uses default name for PlusCal algorithm', () => {
        return assertSymbols(doc, [
            '(* --algorithm',       // No name provided
            'begin',
            '  skip;',
            'end algorithm; *)'
        ], [
            symPlusCal(PLUS_CAL_DEFAULT_NAME, loc(doc.uri, range(0, 0, 3, 17)))
        ]);
    });

});

async function assertSymbols(
    doc: vscode.TextDocument,
    docLines: string[],
    expectSymbols: vscode.SymbolInformation[]
): Promise<void> {
    const docInfos = new TlaDocumentInfos();
    const symbolsProvider = new TlaDocumentSymbolsProvider(docInfos);
    await replaceDocContents(doc, docLines.join('\n'));
    const tokenSrc = new vscode.CancellationTokenSource();
    const symbols = await symbolsProvider.provideDocumentSymbols(doc, tokenSrc.token);
    assert.deepEqual(symbols, expectSymbols);
    assertDocSymbols(doc.uri, docInfos, expectSymbols);
    return undefined;
}

function assertDocSymbols(
    docUri: vscode.Uri,
    docInfos: TlaDocumentInfos,
    expectSymbols: vscode.SymbolInformation[]
) {
    const docSymbolsList = docInfos.get(docUri).symbols;
    expectSymbols.forEach((expSymbol) => {
        const symbol = docSymbolsList.find(s => s.name === expSymbol.name);
        assert.ok(symbol);
    });
}
