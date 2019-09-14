import * as vscode from 'vscode';
import { TlaDocumentInfos } from '../model/documentInfo';
import { getPrevText } from './completions';

export const TLA_OPERATORS = [
    'E', 'A', 'X', 'lnot', 'land', 'lor', 'cdot', 'equiv', 'subseteq', 'in', 'notin', 'intersect',
    'union', 'leq', 'geq', 'cup', 'cap'
];
export const TLA_STARTING_KEYWORDS = [  // These keywords start blocks, should not be in the middle of an expression
    'EXTENDS', 'VARIABLE', 'VARIABLES', 'CONSTANT', 'CONSTANTS', 'ASSUME', 'ASSUMPTION', 'AXIOM', 'THEOREM', 'DEFINE',
    'PROOF', 'LEMMA', 'PROPOSITION', 'COROLLARY', 'QED', 'SUFFICES'
];
export const TLA_OTHER_KEYWORDS = [     // These keywords can be found pretty everywhere
    'LET', 'IN', 'EXCEPT', 'ENABLED', 'UNCHANGED', 'LAMBDA', 'DOMAIN', 'CHOOSE', 'LOCAL', 'RECURSIVE',
    'INSTANCE', 'WITH', 'SUBSET', 'UNION', 'SF_', 'WF_', 'USE', 'DEFS', 'BY', 'DEF', 'PROVE', 'OBVIOUS',
    'NEW', 'PICK', 'HIDE', 'WITNESS', 'HAVE', 'TAKE', 'ACTION', 'OMITTED', 'ONLY', 'STATE', 'TEMPORAL',
    // -- control keywords
    'IF', 'THEN', 'ELSE', 'CASE', 'OTHER',
    // -- other
    'BOOLEAN'
];
export const TLA_CONSTANTS = [ 'TRUE', 'FALSE' ];

const TLA_STARTING_KEYWORD_ITEMS = TLA_STARTING_KEYWORDS.map(w => {
    return new vscode.CompletionItem(w, vscode.CompletionItemKind.Keyword);
});
const TLA_OTHER_KEYWORD_ITEMS = TLA_OTHER_KEYWORDS.map(w => {
    return new vscode.CompletionItem(w, vscode.CompletionItemKind.Keyword);
});
const TLA_CONST_ITEMS = TLA_CONSTANTS.map(w => new vscode.CompletionItem(w, vscode.CompletionItemKind.Constant));
const TLA_OPERATOR_ITEMS = TLA_OPERATORS.map(w => {
    return new vscode.CompletionItem('\\' + w, vscode.CompletionItemKind.Operator);
});
const TLA_INNER_ITEMS = TLA_OTHER_KEYWORD_ITEMS.concat(TLA_CONST_ITEMS);

/**
 * Completes TLA+ text.
 */
export class TlaCompletionItemProvider implements vscode.CompletionItemProvider {
    constructor(
        private docInfos: TlaDocumentInfos
    ) {}

    provideCompletionItems(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken,
        context: vscode.CompletionContext
    ): vscode.ProviderResult<vscode.CompletionList> {
        const prevText = getPrevText(document, position);
        const isOperator = /^.*(?<!\/)\\\w*$/g.test(prevText);  // contains \ before the trailing letters, but not /\
        if (isOperator) {
            return new vscode.CompletionList(TLA_OPERATOR_ITEMS, false);
        }
        const docInfo = this.docInfos.get(document.uri);
        const isPlusCal = docInfo.plusCalRange ? docInfo.plusCalRange.contains(position) : false;
        const isNewLine = /^[\s<>\d\.]*[a-zA-Z]*$/g.test(prevText);
        const symbols = docInfo.symbols || [];
        const symbolInfos = symbols.map(s => new vscode.CompletionItem(s.name, mapKind(s.kind)));
        let items = TLA_INNER_ITEMS.concat(symbolInfos);
        if (isNewLine && !isPlusCal) {
            items = items.concat(TLA_STARTING_KEYWORD_ITEMS);
        }
        return new vscode.CompletionList(items, false);
    }

    resolveCompletionItem?(
        item: vscode.CompletionItem,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<vscode.CompletionItem> {
        switch (item.kind) {
            case vscode.CompletionItemKind.Keyword:
                item.insertText = item.label + ' ';
                break;
            case vscode.CompletionItemKind.Operator:
                item.insertText = item.label.substring(1) + ' ';
                break;
            }
        return item;
    }
}

function mapKind(symbolKind: vscode.SymbolKind): vscode.CompletionItemKind {
    switch (symbolKind) {
        case vscode.SymbolKind.Field:
            return vscode.CompletionItemKind.Field;
        case vscode.SymbolKind.Variable:
            return vscode.CompletionItemKind.Variable;
        case vscode.SymbolKind.Function:
            return vscode.CompletionItemKind.Function;
        case vscode.SymbolKind.Method:
            return vscode.CompletionItemKind.Method;
        case vscode.SymbolKind.Namespace:
        case vscode.SymbolKind.Module:
            return vscode.CompletionItemKind.Module;
        case vscode.SymbolKind.Constant:
            return vscode.CompletionItemKind.Constant;
        }
    return vscode.CompletionItemKind.Text;
}
