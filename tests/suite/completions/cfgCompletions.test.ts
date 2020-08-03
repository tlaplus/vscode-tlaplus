import * as vscode from 'vscode';
import * as assert from 'assert';
import { LANG_TLAPLUS_CFG } from '../../../src/common';
import { TLA_CFG_KEYWORDS, CfgCompletionItemProvider } from '../../../src/completions/cfgCompletions';
import { parseDocInfo, replaceDocContents } from '../document';
import { assertSymbolClass } from './completion';
import { TLA_CONSTANTS } from '../../../src/completions/tlaCompletions';

const EXPECT_NOTHING = 0;
const EXPECT_CFG_KEYWORDS = 1;
const EXPECT_CONSTANTS = 8;

suite('Cfg Completions Provider Test Suite', () => {
    let doc: vscode.TextDocument;

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({ language: LANG_TLAPLUS_CFG });
    });

    suiteTeardown(async () => {
        await vscode.window.showTextDocument(doc, {preview: true, preserveFocus: false});
        return vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Completes on new line', () => {
        return assertCompletions(doc, [
            '${i}'
        ], EXPECT_CFG_KEYWORDS);
    });

    test('Doesn\'t complete in the middle of a line', () => {
        return assertCompletions(doc, [
            'CONSTANTS Foo, B${a}'
        ], EXPECT_NOTHING);
    });

    test('Completes boolean constants after CHECK_DEADLOCK', () => {
        return assertCompletions(doc, [
            'CHECK_DEADLOCK ${e}'
        ], EXPECT_CONSTANTS);
    });
});

async function assertCompletions(
    doc: vscode.TextDocument,
    docLines: string[],
    expectFlags: number
): Promise<void> {
    const docInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, docInfo.lines.join('\n'));
    const completionsProvider = new CfgCompletionItemProvider();
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
    if ((expectFlags & EXPECT_CFG_KEYWORDS) !== 0) {
        total += assertCfgKeywords(completions);
    }
    if ((expectFlags & EXPECT_CONSTANTS) !== 0) {
        total += assertConstants(completions);
    }
    assert.equal(
        total,
        completions.items.length,
        `Expected ${total} completions, found ${completions.items.length}:'
            + '\n${completions.items.map((it) => it.label).join(', ')}`
    );
}

function assertCfgKeywords(list: vscode.CompletionList): number {
    return assertSymbolClass(TLA_CFG_KEYWORDS, vscode.CompletionItemKind.Keyword, list);
}

function assertConstants(list: vscode.CompletionList): number {
    return assertSymbolClass(TLA_CONSTANTS, vscode.CompletionItemKind.Constant, list);
}
