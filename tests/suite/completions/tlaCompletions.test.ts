import * as vscode from 'vscode';
import * as assert from 'assert';
import { LANG_TLAPLUS } from '../../../src/common';
import { TlaCompletionItemProvider, TLA_CONSTANTS, TLA_STARTING_KEYWORDS, TLA_PROOF_STARTING_KEYWORDS,
    TLA_OTHER_KEYWORDS, TLA_OPERATORS, TLA_STD_MODULES } from '../../../src/completions/tlaCompletions';
import { parseDocInfo, replaceDocContents } from '../document';
import { assertCompletion, assertSymbolClass, createTestDocInfos } from './completion';

const EXPECT_NOTHING = 0;
const EXPECT_STARTING_KEYWORDS = 1;
const EXPECT_PROOF_STARTING_KEYWORDS = 2;
const EXPECT_OTHER_KEYWORDS = 4;
const EXPECT_CONSTANTS = 8;
const EXPECT_OPERATORS = 16;
const EXPECT_SYMBOLS = 32;
const EXPECT_STD_MODULES = 64;
const EXPECT_INNER_CLASS = EXPECT_OTHER_KEYWORDS | EXPECT_CONSTANTS | EXPECT_SYMBOLS;

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
            '${i}'
        ], EXPECT_STARTING_KEYWORDS | EXPECT_INNER_CLASS);
    });

    test('Treats step numbers as new line in proof block', () => {
        return assertCompletions(doc, [
            '<1>. ${t}'
        ], EXPECT_PROOF_STARTING_KEYWORDS | EXPECT_INNER_CLASS);
    });

    test('Treats subsection numbers as new line in proof block', () => {
        return assertCompletions(doc, [
            '<12>.4 ${t}'
        ], EXPECT_PROOF_STARTING_KEYWORDS | EXPECT_INNER_CLASS);
    });

    test('Reckognizes letters in proof step numbers', () => {
        return assertCompletions(doc, [
            '<8>.a ${t}'
        ], EXPECT_PROOF_STARTING_KEYWORDS | EXPECT_INNER_CLASS);
    });

    test('Completes all but operators after /\\', () => {
        return assertCompletions(doc, [
            'Foo == /\\${a}'
        ], EXPECT_INNER_CLASS);
    });

    test('Completes only operators after \\', () => {
        return assertCompletions(doc, [
            '\\${i}'
        ], EXPECT_OPERATORS);
    });

    test('Completes only operators after \\ followed by symbols', () => {
        return assertCompletions(doc, [
            '\\e${q}'
        ], EXPECT_OPERATORS);
    });

    test('Completes all but operators after \\ followed by a space', () => {
        return assertCompletions(doc, [
            '\\ e${q}'
        ], EXPECT_INNER_CLASS);
    });

    test('Completes std modules after EXTENDS', () => {
        return assertCompletions(doc, [
            'EXTENDS ${r}'
        ], EXPECT_STD_MODULES);
    });
});

async function assertCompletions(
    doc: vscode.TextDocument,
    docLines: string[],
    expectFlags: number
): Promise<void> {
    const docInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, docInfo.lines.join('\n'));
    const docInfos = createTestDocInfos(doc.uri);
    const completionsProvider = new TlaCompletionItemProvider(docInfos);
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
    if ((expectFlags & EXPECT_STARTING_KEYWORDS) !== 0) {
        total += assertStartingKeywords(completions);
    }
    if ((expectFlags & EXPECT_PROOF_STARTING_KEYWORDS) !== 0) {
        total += assertProofStartingKeywords(completions);
    }
    if ((expectFlags & EXPECT_OTHER_KEYWORDS) !== 0) {
        total += assertOtherKeywords(completions);
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
    if ((expectFlags & EXPECT_STD_MODULES) !== 0) {
        total += assertStdModules(completions);
    }
    assert.equal(
        total,
        completions.items.length,
        `Expected ${total} completions, found ${completions.items.length}:'
            + '\n${completions.items.map((it) => it.label).join(', ')}`
    );
}

function assertStartingKeywords(list: vscode.CompletionList): number {
    return assertSymbolClass(TLA_STARTING_KEYWORDS, vscode.CompletionItemKind.Keyword, list);
}

function assertProofStartingKeywords(list: vscode.CompletionList): number {
    return assertSymbolClass(TLA_PROOF_STARTING_KEYWORDS, vscode.CompletionItemKind.Keyword, list);
}

function assertOtherKeywords(list: vscode.CompletionList): number {
    return assertSymbolClass(TLA_OTHER_KEYWORDS, vscode.CompletionItemKind.Keyword, list);
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

function assertStdModules(list: vscode.CompletionList) {
    return assertSymbolClass(TLA_STD_MODULES, vscode.CompletionItemKind.Module, list);
}
