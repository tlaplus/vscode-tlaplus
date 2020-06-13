import * as vscode from 'vscode';
import * as assert from 'assert';
import { LANG_TLAPLUS } from '../../../src/common';
import { loc, pos } from '../shortcuts';
import { parseDocInfo, replaceDocContents } from '../document';
import { TlaDocumentInfos } from '../../../src/model/documentInfo';
import { TlaDeclarationsProvider } from '../../../src/declarations/tlaDeclarations';
import { TlaDefinitionsProvider } from '../../../src/declarations/tlaDeclarations';
import { TlaDocumentSymbolsProvider } from '../../../src/symbols/tlaSymbols';

suite('TLA Declarations Provider Test Suite', () => {
    let doc: vscode.TextDocument;

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({ language: LANG_TLAPLUS });
    });

    test('Finds symbol in TLA+ module', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            'Foo == TRUE',
            'Bar == Fo${o}',
            '===='
        ], [
            loc(doc.uri, pos(1, 0))
        ]);
    });

    test('Ignores symbols that go after the current position', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            'Bar == Fo${o}',
            'Foo == TRUE',
            '===='
        ], []);
    });

    test('Ignores declaration inside itself', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            '/* foo',
            'F${o}o == TRUE',
            '===='
        ], [
            loc(doc.uri, pos(2, 0))
        ]);
    });

    test('Finds multiple declarations', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            'CONSTANTS Foo',
            'Foo(x) == x + 1',
            'Bar == ${F}oo',
            '===='
        ], [
            loc(doc.uri, pos(1, 10)),
            loc(doc.uri, pos(2, 0))
        ]);
    });

    test('Finds declarations of primed operators', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            'VARIABLES bar',
            "Next == /\\ b${a}r' = bar + 1",
            '===='
        ], [
            loc(doc.uri, pos(1, 10))
        ]);
    });

    test('Finds symbols in PlusCal algorithm', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            '(*--algorithm foo',
            'variable x',
            'define',
            '  Foo == TRUE',
            'end define',
            'begin',
            '  x := F${o}o',
            'end algorithm; *)',
            '===='
        ], [
            loc(doc.uri, pos(4, 0))
        ]);
    });

    test('Finds TLA+ symbols in PlusCal algorithm', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            'Foo == TRUE',
            '(*--algorithm foo',
            'variables x',
            'begin',
            '  x := F${o}o',
            'end algorithm; *)',
            '===='
        ], [
            loc(doc.uri, pos(1, 0))
        ]);
    });

    test('Ignores PlusCal declarations in TLA+', () => {
        return assertDeclarations(doc, [
            '---- MODULE foo ----',
            '(*--algorithm foo',
            'variables xyz',
            'begin',
            '  x := Foo',
            'end algorithm; *)',
            'Foo == UNCHANGED x${y}z',
            '===='
        ], []);
    });

    test('Find variable definition in TLA+ module', () => {
        return assertDefinitions(doc, [
            '---- MODULE foo ----',
            'VARIABLE x',
            'A == ${x}',
            '===='
        ], [
            loc(doc.uri, pos(1, 9))
        ]);
    });

    test('Find operator definition in TLA+ module', () => {
        return assertDefinitions(doc, [
            '---- MODULE foo ----',
            'Foo(a) == 1',
            'Bar == ${F}oo',
            '===='
        ], [
            loc(doc.uri, pos(1, 0))
        ]);
    });

    test('Find constant operator definition in TLA+ module', () => {
        return assertDefinitions(doc, [
            '---- MODULE foo ----',
            'Foo == 1',
            'Bar == ${F}oo',
            '===='
        ], [
            loc(doc.uri, pos(1, 0))
        ]);
    });

    test('Find multiple definitions in TLA+ module', () => {
        return assertDefinitions(doc, [
            '---- MODULE foo ----',
            'CONSTANT Foo',
            'Foo == 1',
            'Bar == ${F}oo',
            '===='
        ], [
            loc(doc.uri, pos(1, 9)),
            loc(doc.uri, pos(2, 0))
        ]);
    });

    test('Find constant definition in TLA+ module', () => {
        return assertDefinitions(doc, [
            '---- MODULE foo ----',
            'CONSTANT Foo',
            'Bar == ${F}oo',
            '===='
        ], [
            loc(doc.uri, pos(1, 9))
        ]);
    });

    test('Ignores PlusCal definitions in TLA+', () => {
        return assertDefinitions(doc, [
            '---- MODULE foo ----',
            '(*--algorithm foo',
            'variables xyz',
            'begin',
            '  x := Foo',
            'end algorithm; *)',
            'Foo == UNCHANGED x${y}z',
            '===='
        ], []);
    });
});

async function assertDeclarations(
    doc: vscode.TextDocument,
    docLines: string[],
    expectLocations: vscode.Location[]
): Promise<void> {
    const testDocInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, testDocInfo.lines.join('\n'));
    const docInfos = new TlaDocumentInfos();
    const declProvider = new TlaDeclarationsProvider(docInfos);
    const symbolsProvider = new TlaDocumentSymbolsProvider(docInfos);
    const tokenSrc = new vscode.CancellationTokenSource();
    await symbolsProvider.provideDocumentSymbols(doc, tokenSrc.token);
    const locations = await declProvider.provideDeclaration(doc, testDocInfo.position, tokenSrc.token);
    assert.deepEqual(locations, expectLocations);
    return undefined;
}

async function assertDefinitions(
    doc: vscode.TextDocument,
    docLines: string[],
    expectLocations: vscode.Location[]
): Promise<void> {
    const testDocInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, testDocInfo.lines.join('\n'));
    const docInfos = new TlaDocumentInfos();
    const defProvider = new TlaDefinitionsProvider(docInfos);
    const symbolsProvider = new TlaDocumentSymbolsProvider(docInfos);
    const tokenSrc = new vscode.CancellationTokenSource();
    await symbolsProvider.provideDocumentSymbols(doc, tokenSrc.token);
    const locations = await defProvider.provideDefinition(doc, testDocInfo.position, tokenSrc.token);
    assert.deepEqual(locations, expectLocations);
    return undefined;
}
