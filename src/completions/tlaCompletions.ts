import * as vscode from 'vscode';
import { TlaDocumentInfos } from '../model/documentInfo';
import { getPrevText } from './completions';

export const TLA_OPERATORS = [
    'land', 'lor', 'implies',
    'lnot', 'equiv', 'triangleq',
    'in', 'notin', 'ne',
    'll', 'gg', '[]',
    'leq', 'geq', '<>',
    '~>', 'prec', 'succ',
    '-+->', 'preceq', 'succeq',
    'div', 'subseteq', 'supseteq',
    'cdot', 'subset', 'supset',
    'o', 'sqsubset', 'sqsupset',
    'bullet', 'sqsubseteq', 'sqsupseteq',
    'star', 'vdash', 'dashv',
    'bigcirc', 'models', 'vDash',
    'sim', 'maps', 'leftarrow',
    'simeq', 'cap', 'cup',
    'asymp', 'sqcap', 'sqcup',
    'approx', 'oplus', 'uplus',
    'cong', 'ominus', 'X',
    'doteq', 'odot', 'wr',
    'otimes', 'propto', 'oslash',
    'E', 'A', 'EE', 'AA',
    // Aliases
    'intersect', 'union', 'times', 'circ',
    'forall', 'exists', 'neg'
];

const enableUnicodeAutocomplete = vscode.workspace.getConfiguration()
    .get<boolean>('tlaplus.unicode.autocomplete', false);

export const TLA_UNICODE_OPERATORS: Map<string, string> = new Map([
    ['land', '∧'], ['lor', '∨'], ['implies', '⇒'],
    ['lnot', '¬'], ['equiv', '≡'], ['triangleq', '≜'],
    ['in', '∈'], ['notin', '∉'], ['ne', '≠'],
    ['ll', '≪'], ['gg', '≫'], ['[]', '□'],
    ['leq', '≤'], ['geq', '≥'], ['<>', '◊'],
    ['~>', '↝'], ['prec', '≺'], ['succ', '≻'],
    ['-+->', '⇸'], ['preceq', '⪯'], ['succeq', '⪰'],
    ['div', '÷'], ['subseteq', '⊆'], ['supseteq', '⊇'],
    ['cdot', '⋅'], ['subset', '⊂'], ['supset', '⊃'],
    ['o', '∘'], ['sqsubset', '⊏'], ['sqsupset', '⊐'],
    ['bullet', '●'], ['sqsubseteq', '⊑'], ['sqsupseteq', '⊒'],
    ['star', '⋆'], ['vdash', '⊢'], ['dashv', '⊣'],
    ['bigcirc', '◯'], ['models', '⊨'], ['vDash', '=|'],
    ['sim', '∼'], ['maps', '→'], ['leftarrow', '←'],
    ['simeq', '≃'], ['cap', '∩'], ['cup', '∪'],
    ['asymp', '≍'], ['sqcap', '⊓'], ['sqcup', '⊔'],
    ['approx', '≈'], ['oplus', '⊕'], ['uplus', '⊎'],
    ['cong', '≅'], ['ominus', '⊖'], ['X', '×'],
    ['doteq', '≐'], ['odot', '⊙'], ['wr', '≀'],
    ['otimes', '⊗'], ['propto', '∝'], ['oslash', '⊘'],
    ['E', '∃'], ['A', '∀'], ['EE', '∃'], ['AA', '∀'],
    // Aliases
    ['times', '×'], ['circ', '∘'], ['intersect', '∩'], ['union', '∪'],
    ['forall', '∀'], ['exists', '∃'], ['neg', '¬'],
]);

export const TLA_STARTING_KEYWORDS = [  // These keywords start blocks, and should not be in the middle of an expression
    'EXTENDS', 'VARIABLE', 'VARIABLES', 'CONSTANT', 'CONSTANTS', 'ASSUME', 'ASSUMPTION', 'AXIOM', 'THEOREM',
    'PROOF', 'LEMMA', 'PROPOSITION', 'COROLLARY', 'RECURSIVE'
];
export const TLA_PROOF_STARTING_KEYWORDS = [ // These keywords start proof steps
    'DEFINE', 'QED', 'HIDE', 'SUFFICES', 'PICK', 'HAVE', 'TAKE', 'WITNESS'
];
export const TLA_OTHER_KEYWORDS = [     // These keywords can be found pretty everywhere
    'LET', 'IN', 'EXCEPT', 'ENABLED', 'UNCHANGED', 'LAMBDA', 'DOMAIN', 'CHOOSE', 'LOCAL',
    'INSTANCE', 'WITH', 'SUBSET', 'UNION', 'SF_', 'WF_', 'USE', 'BY', 'DEF', 'DEFS', 'PROVE', 'OBVIOUS',
    'NEW', 'ACTION', 'OMITTED', 'ONLY', 'STATE', 'TEMPORAL',
    // -- control keywords
    'IF', 'THEN', 'ELSE', 'CASE', 'OTHER',
    // -- other
    'BOOLEAN'
];
export const TLA_CONSTANTS = ['TRUE', 'FALSE'];
export const TLA_STD_MODULES = [
    'Bags', 'FiniteSets', 'Integers', 'Naturals', 'Randomization', 'Reals', 'RealTime', 'Sequences', 'TLC'
];

const TLA_STARTING_KEYWORD_ITEMS = TLA_STARTING_KEYWORDS.map(w => {
    return new vscode.CompletionItem(w, vscode.CompletionItemKind.Keyword);
});
const TLA_PROOF_STARTING_KEYWORD_ITEMS = TLA_PROOF_STARTING_KEYWORDS.map(w => {
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
const TLA_STD_MODULE_ITEMS = TLA_STD_MODULES.map(m => {
    return new vscode.CompletionItem(m, vscode.CompletionItemKind.Module);
});

/**
 * Resolves an operator completion item, setting the appropriate insertText.
 * Exported for testing purposes.
 */
export function resolveOperatorCompletion(
    item: vscode.CompletionItem,
    useUnicode: boolean
): vscode.CompletionItem {
    const operatorName = item.label.toString().substring(1); // Remove leading backslash
    const unicodeSymbol = TLA_UNICODE_OPERATORS.get(operatorName);
    item.insertText = (useUnicode && unicodeSymbol ? unicodeSymbol : '\\' + operatorName);
    return item;
}

/**
 * Completes TLA+ text.
 */
export class TlaCompletionItemProvider implements vscode.CompletionItemProvider {
    constructor(
        private readonly docInfos: TlaDocumentInfos
    ) { }

    provideCompletionItems(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken,
        context: vscode.CompletionContext
    ): vscode.ProviderResult<vscode.CompletionList> {
        const prevText = getPrevText(document, position);
        if (prevText.startsWith('EXTENDS')) {
            return new vscode.CompletionList(TLA_STD_MODULE_ITEMS, false);
        }
        if (prevText.startsWith('CONSTANT') || prevText.startsWith('RECURSIVE')) {
            return new vscode.CompletionList([], false);
        }
        const isOperator = /^.*(?<!\/)\\\w*$/g.test(prevText);  // contains \ before the trailing letters, but not /\
        if (isOperator) {
            // Set an explicit replacement range that includes the backslash.
            // Without this, VS Code uses word-based replacement which doesn't consider '\'
            // part of a word, so typing '\in' and selecting a completion would only replace
            // 'in', leaving the backslash behind (e.g., '\in' -> '\∈' instead of '∈').
            const match = prevText.match(/\\(\w*)$/);
            if (match) {
                const backslashCol = prevText.length - match[0].length;
                const range = new vscode.Range(
                    new vscode.Position(position.line, backslashCol),
                    position
                );
                const items = TLA_OPERATORS.map(op => {
                    const item = new vscode.CompletionItem('\\' + op, vscode.CompletionItemKind.Operator);
                    item.range = range;
                    return item;
                });
                return new vscode.CompletionList(items, false);
            }
            return new vscode.CompletionList(TLA_OPERATOR_ITEMS, false);
        }
        const docInfo = this.docInfos.get(document.uri);
        const symbols = docInfo.symbols || [];
        const symbolInfos = symbols.map(s => new vscode.CompletionItem(s.name, mapKind(s.kind)));
        let items = TLA_INNER_ITEMS.concat(symbolInfos);
        if (!docInfo.isPlusCalAt(position)) {
            const isProofStep = /^\s*<\d+>[<>\d.a-zA-Z]*\s+[a-zA-Z]*$/g.test(prevText);
            const isNewLine = /^\s*[a-zA-Z]*$/g.test(prevText);
            if (isProofStep) {
                items = items.concat(TLA_PROOF_STARTING_KEYWORD_ITEMS);
            } else if (isNewLine) {
                items = items.concat(TLA_STARTING_KEYWORD_ITEMS);
            }
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
                return resolveOperatorCompletion(item, enableUnicodeAutocomplete);
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
