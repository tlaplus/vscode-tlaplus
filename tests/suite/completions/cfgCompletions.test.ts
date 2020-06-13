import * as vscode from 'vscode';
import * as assert from 'assert';
import { LANG_TLAPLUS_CFG } from '../../../src/common';
import { CfgCompletionItemProvider, TLA_CFG_KEYWORDS } from '../../../src/completions/cfgCompletions';
import { parseDocInfo, replaceDocContents } from '../document';

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
        ], true);
    });

    test('Doesn\'t complete in the middle of a line', () => {
        return assertCompletions(doc, [
            'CONSTANTS Foo, B${a}'
        ], false);
    });
});

async function assertCompletions(
    doc: vscode.TextDocument,
    docLines: string[],
    expectCompletions: boolean
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
    if (!completions && expectCompletions) {
        assert.fail('No completions returned when expected');
    }
    if (completions && completions.items.length > 0 && !expectCompletions) {
        assert.fail('Completions returned when not expected');
    }
    if (expectCompletions && completions) {
        assert.equal(completions.items.length, TLA_CFG_KEYWORDS.length);
    }
}
