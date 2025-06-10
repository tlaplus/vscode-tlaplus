import * as vscode from 'vscode';
import { TlaDocumentInfos } from '../model/documentInfo';
import { getPrevText } from './completions';
import { ModuleSymbolProvider } from '../symbols/moduleSymbolProvider';

export const TLA_OPERATORS = [
    'E', 'A', 'X', 'lnot', 'land', 'lor', 'cdot', 'equiv', 'subseteq', 'in', 'notin', 'intersect',
    'union', 'leq', 'geq', 'cup', 'cap'
];
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
export const TLA_CONSTANTS = [ 'TRUE', 'FALSE' ];
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
 * Completes TLA+ text.
 */
export class TlaCompletionItemProvider implements vscode.CompletionItemProvider {
    private moduleSymbolsCache: vscode.CompletionItem[] = [];
    private cacheTimestamp = 0;
    private readonly CACHE_TTL = 60000; // 1 minute

    constructor(
        private readonly docInfos: TlaDocumentInfos,
        private readonly symbolProvider: ModuleSymbolProvider
    ) {}

    async provideCompletionItems(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken,
        context: vscode.CompletionContext
    ): Promise<vscode.CompletionList> {
        const prevText = getPrevText(document, position);

        // Module completions after EXTENDS
        if (prevText.startsWith('EXTENDS')) {
            // Get all available modules from symbol provider
            const moduleSymbols = await this.getModuleSymbols();
            const moduleNames = new Set<string>();

            // Extract unique module names
            for (const item of moduleSymbols) {
                if (item.detail) {
                    const match = item.detail.match(/From module: (\w+)/);
                    if (match) {
                        moduleNames.add(match[1]);
                    }
                }
            }

            // Create completion items for modules
            const moduleItems = Array.from(moduleNames).map(name =>
                new vscode.CompletionItem(name, vscode.CompletionItemKind.Module)
            );

            // Add standard modules
            const allModuleItems = TLA_STD_MODULE_ITEMS.concat(moduleItems);
            return new vscode.CompletionList(allModuleItems, false);
        }

        if (prevText.startsWith('CONSTANT') || prevText.startsWith('RECURSIVE')) {
            return new vscode.CompletionList([], false);
        }

        const isOperator = /^.*(?<!\/)\\\w*$/g.test(prevText);  // contains \ before the trailing letters, but not /\
        if (isOperator) {
            return new vscode.CompletionList(TLA_OPERATOR_ITEMS, false);
        }

        // Get document symbols
        const docInfo = this.docInfos.get(document.uri);
        const symbols = docInfo.symbols || [];
        const symbolInfos = symbols.map(s => new vscode.CompletionItem(s.name, mapKind(s.kind)));

        // Get module symbols
        const moduleSymbols = await this.getModuleSymbols();

        // Combine all completion items
        let items = TLA_INNER_ITEMS.concat(symbolInfos).concat(moduleSymbols);

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
                item.insertText = item.label.toString().substring(1) + ' ';
                break;
        }
        return item;
    }

    /**
     * Gets module symbols with caching.
     */
    private async getModuleSymbols(): Promise<vscode.CompletionItem[]> {
        const now = Date.now();

        // Check cache
        if (this.moduleSymbolsCache.length > 0 && now - this.cacheTimestamp < this.CACHE_TTL) {
            return this.moduleSymbolsCache;
        }

        try {
            // Get all symbols from the symbol provider
            const symbols = await this.symbolProvider.getAllSymbols();

            // Convert to completion items
            this.moduleSymbolsCache = symbols.map(symbol => {
                const item = new vscode.CompletionItem(
                    symbol.name,
                    mapKind(symbol.kind)
                );

                // Add module information
                item.detail = `From module: ${symbol.module}`;

                // Add documentation
                if (symbol.documentation) {
                    item.documentation = new vscode.MarkdownString(symbol.documentation);
                }

                // Add signature for functions
                if (symbol.arity && symbol.arity > 0) {
                    const params = Array(symbol.arity).fill('_').join(', ');
                    item.insertText = new vscode.SnippetString(`${symbol.name}(\${1:${params}})`);
                }

                return item;
            });

            this.cacheTimestamp = now;
            return this.moduleSymbolsCache;
        } catch (error) {
            console.error('Failed to get module symbols:', error);
            return [];
        }
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
