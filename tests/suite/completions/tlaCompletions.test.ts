import * as vscode from 'vscode';
import * as assert from 'assert';
import { LANG_TLAPLUS } from '../../../src/common';
import { TlaCompletionItemProvider, TLA_CONSTANTS, TLA_KEYWORDS, TLA_OPERATORS
    } from '../../../src/completions/tlaCompletions';
import { parseDocInfo, replaceDocContents } from '../document';
import { loc, pos } from '../shortcuts';

const EXPECT_NOTHING = 0;
const EXPECT_KEYWORDS = 1;
const EXPECT_CONSTANTS = 2;
const EXPECT_OPERATORS = 4;
const EXPECT_SYMBOLS = 8;
const EXPECT_ALL_BUT_OPERATORS = EXPECT_KEYWORDS | EXPECT_CONSTANTS | EXPECT_SYMBOLS;

const PREFIXED_OPERATORS = TLA_OPERATORS.map((op) => '\\' + op);

suite('TLA Completions Provider Test Suite', () => {
    let doc: vscode.TextDocument;

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({ language: LANG_TLAPLUS });
    });

    suiteTeardown(async () => {
        await vscode.window.showTextDocument(doc, {preview: true, preserveFocus: false});
        return vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Completes all but operators on new line', () => {
        return assertCompletions(doc, [
            '{i}'
        ], EXPECT_ALL_BUT_OPERATORS);
    });

    test('Completes all but operators after /\\', () => {
        return assertCompletions(doc, [
            'Foo == /\\{a}'
        ], EXPECT_ALL_BUT_OPERATORS);
    });

    test('Completes only operators after \\', () => {
        return assertCompletions(doc, [
            '\\{i}'
        ], EXPECT_OPERATORS);
    });

    test('Completes only operators after \\ followed by symbols', () => {
        return assertCompletions(doc, [
            '\\e{q}'
        ], EXPECT_OPERATORS);
    });

    test('Completes all but operators after \\ followed by a space', () => {
        return assertCompletions(doc, [
            '\\ e{q}'
        ], EXPECT_ALL_BUT_OPERATORS);
    });

});

async function assertCompletions(
    doc: vscode.TextDocument,
    docLines: string[],
    expectFlags: number
): Promise<void> {
    const docInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, docInfo.lines.join('\n'));
    const docSymbols = createTestSymsols(doc.uri);
    const completionsProvider = new TlaCompletionItemProvider(docSymbols);
    const tokenSrc = new vscode.CancellationTokenSource();
    const ctx: vscode.CompletionContext = {
        triggerKind: vscode.CompletionTriggerKind.TriggerCharacter,
        triggerCharacter: docInfo.char
    };
    const completions = await completionsProvider.provideCompletionItems(doc, docInfo.position, tokenSrc.token, ctx);
    if (!completions) {
        assert.equal(EXPECT_NOTHING, expectFlags, `No completions returned when expected ${expectFlags}`);
        return;
    }
    assert.equal(false, completions.isIncomplete, 'Completions list is expected to be complete');
    let total = 0;
    if ((expectFlags & EXPECT_KEYWORDS) !== 0) {
        total += assertKeywords(completions);
    }
    if ((expectFlags & EXPECT_CONSTANTS) !== 0) {
        total += assertConstants(completions);
    }
    if ((expectFlags & EXPECT_OPERATORS) !== 0) {
        total += assertOperators(completions);
    }
    if ((expectFlags & EXPECT_SYMBOLS) !== 0) {
        total += assertSymbols(completions);
    }
    assert.equal(total, completions.items.length, `Expected ${total} completions, found ${completions.items.length}`);
    return undefined;
}

function assertKeywords(list: vscode.CompletionList): number {
    return assertSymbolClass(TLA_KEYWORDS, vscode.CompletionItemKind.Keyword, list);
}

function assertConstants(list: vscode.CompletionList): number {
    return assertSymbolClass(TLA_CONSTANTS, vscode.CompletionItemKind.Constant, list);
}

function assertOperators(list: vscode.CompletionList): number {
    return assertSymbolClass(PREFIXED_OPERATORS, vscode.CompletionItemKind.Operator, list);
}

function assertSymbols(list: vscode.CompletionList) {
    assertCompletion('Foo', vscode.CompletionItemKind.Field, list);
    return 1;
}

function assertSymbolClass(labels: string[], expKind: vscode.CompletionItemKind, list: vscode.CompletionList): number {
    labels.forEach((label) => {
        assertCompletion(label, expKind, list);
    });
    return labels.length;
}

function assertCompletion(
    label: string,
    expectKind: vscode.CompletionItemKind,
    list: vscode.CompletionList
) {
    const comp = list.items.find((c) => c.label === label);
    if (comp) {
        assert.equal(comp.kind, expectKind);
    } else {
        assert.fail(`Completion ${label} not found`);
    }
}

function createTestSymsols(docUri: vscode.Uri): Map<vscode.Uri, vscode.SymbolInformation[]> {
    const symbolsList = [];
    symbolsList.push(
        new vscode.SymbolInformation('Foo', vscode.SymbolKind.Field, 'test', loc(docUri, pos(0, 0)))
    );
    const symbols = new Map<vscode.Uri, vscode.SymbolInformation[]>();
    symbols.set(docUri, symbolsList);
    return symbols;
}
