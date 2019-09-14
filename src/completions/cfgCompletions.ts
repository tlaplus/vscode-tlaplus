import * as vscode from 'vscode';
import { getPrevText } from './completions';

export const TLA_CFG_KEYWORDS = [
    'SPECIFICATION', 'INVARIANT', 'INVARIANTS', 'PROPERTY', 'PROPERTIES', 'CONSTANT', 'CONSTANTS', 'INIT',
    'NEXT', 'SYMMETRY', 'CONSTRAINT', 'CONSTRAINTS', 'ACTION_CONSTRAINT', 'ACTION_CONSTRAINTS', 'VIEW'
];
const KEYWORD_ITEMS = TLA_CFG_KEYWORDS.map(w => {
    return new vscode.CompletionItem(w, vscode.CompletionItemKind.Keyword);
});

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
