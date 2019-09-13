import * as vscode from 'vscode';

export const TLA_OPERATORS = [
    'E', 'A', 'X', 'o', 'lnot', 'land', 'lor', 'cdot', 'equiv', 'subseteq', 'in', 'notin', 'intersect',
    'union', 'leq', 'geq', 'cup', 'cap'
];
export const TLA_KEYWORDS = [
    'EXTENDS', 'VARIABLE', 'VARIABLES', 'LET', 'IN', 'EXCEPT', 'ENABLED', 'UNCHANGED', 'LAMBDA', 'DOMAIN',
    'CONSTANT', 'CONSTANTS', 'CHOOSE', 'LOCAL', 'ASSUME', 'ASSUMPTION', 'AXIOM', 'RECURSIVE', 'INSTANCE', 'WITH',
    'THEOREM', 'SUBSET', 'UNION', 'SF_', 'WF_', 'USE', 'DEFS', 'BY', 'DEF', 'SUFFICES', 'PROVE', 'OBVIOUS', 'NEW',
    'QED', 'RECURSIVE', 'PICK', 'HIDE', 'DEFINE', 'WITNESS', 'HAVE', 'TAKE', 'PROOF', 'ACTION', 'COROLLARY', 'LEMMA',
    'OMITTED', 'ONLY', 'PROPOSITION', 'STATE', 'TEMPORAL',
    // -- control keywords
    'IF', 'THEN', 'ELSE', 'CASE', 'OTHER',
    // -- other
    'BOOLEAN'
];
export const TLA_CONSTANTS = [ 'TRUE', 'FALSE' ];

const TLA_KEYWORD_ITEMS = TLA_KEYWORDS.map(w => new vscode.CompletionItem(w, vscode.CompletionItemKind.Keyword));
const TLA_CONST_ITEMS = TLA_CONSTANTS.map(w => new vscode.CompletionItem(w, vscode.CompletionItemKind.Constant));
const TLA_OPERATOR_ITEMS = TLA_OPERATORS.map(w => {
    return new vscode.CompletionItem('\\' + w, vscode.CompletionItemKind.Operator);
});
const TLA_ITEMS = TLA_KEYWORD_ITEMS.concat(TLA_CONST_ITEMS);

/**
 * Completes TLA+ text.
 */
export class TlaCompletionItemProvider implements vscode.CompletionItemProvider {
    constructor(
        private docSymbols: ReadonlyMap<vscode.Uri, ReadonlyArray<vscode.SymbolInformation>>
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
        const symbols = this.docSymbols.get(document.uri) || [];
        const symbolInfos = symbols.map(s => new vscode.CompletionItem(s.name, mapKind(s.kind)));
        const items = TLA_ITEMS.concat(symbolInfos);
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

function getPrevText(document: vscode.TextDocument, position: vscode.Position): string {
    if (position.character === 0) {
        return '';
    }
    const prevText = document.lineAt(position.line).text.substring(0, position.character);
    return prevText;
}
