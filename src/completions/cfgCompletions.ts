import * as vscode from 'vscode';
import { getPrevText } from './completions';
import { TLA_CONSTANTS } from './tlaCompletions';

export const TLA_CFG_KEYWORDS = [
    'SPECIFICATION', 'INVARIANT', 'INVARIANTS', 'PROPERTY', 'PROPERTIES', 'CONSTANT', 'CONSTANTS', 'INIT',
    'NEXT', 'SYMMETRY', 'CONSTRAINT', 'CONSTRAINTS', 'ACTION_CONSTRAINT', 'ACTION_CONSTRAINTS', 'VIEW',
    'CHECK_DEADLOCK', 'POSTCONDITION', 'ALIAS'
];

const KEYWORD_ITEMS = TLA_CFG_KEYWORDS.map(w => {
    return new vscode.CompletionItem(w, vscode.CompletionItemKind.Keyword);
});
const TLA_CONST_ITEMS = TLA_CONSTANTS.map(w => new vscode.CompletionItem(w, vscode.CompletionItemKind.Constant));

/**
 * Completes text in .cfg files.
 */
export class CfgCompletionItemProvider implements vscode.CompletionItemProvider {
    provideCompletionItems(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken,
        context: vscode.CompletionContext
    ): vscode.ProviderResult<vscode.CompletionList> {
        const prevText = getPrevText(document, position);
        const isNewLine = /^\s*[a-zA-Z]*$/g.test(prevText);
        if (prevText.startsWith('CHECK_DEADLOCK')) {
            return new vscode.CompletionList(TLA_CONST_ITEMS, false);
        }
        return new vscode.CompletionList(isNewLine ? KEYWORD_ITEMS : [], false);
    }

    resolveCompletionItem?(
        item: vscode.CompletionItem,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.CompletionItem> {
        item.insertText = item.label + ' ';
        return item;
    }
}
