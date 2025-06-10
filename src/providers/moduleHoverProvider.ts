import * as vscode from 'vscode';
import { ModuleSymbolProvider } from '../symbols/moduleSymbolProvider';

/**
 * Provides hover information for TLA+ module operators and symbols.
 */
export class ModuleHoverProvider implements vscode.HoverProvider {
    constructor(
        private readonly symbolProvider: ModuleSymbolProvider
    ) {}

    async provideHover(
        document: vscode.TextDocument,
        position: vscode.Position,
        token: vscode.CancellationToken
    ): Promise<vscode.Hover | undefined> {
        // Get the word at the current position
        const wordRange = document.getWordRangeAtPosition(position, /[a-zA-Z_][a-zA-Z0-9_]*/);
        if (!wordRange) {
            return undefined;
        }

        const word = document.getText(wordRange);
        if (!word) {
            return undefined;
        }

        // Check if this is a qualified reference (Module!Symbol)
        const lineText = document.lineAt(position.line).text;
        const beforeWord = lineText.substring(0, wordRange.start.character);
        const qualifiedMatch = beforeWord.match(/([a-zA-Z_][a-zA-Z0-9_]*)!$/);

        let symbols;
        if (qualifiedMatch) {
            // Qualified reference - search in specific module
            const moduleName = qualifiedMatch[1];
            symbols = await this.symbolProvider.getSymbolsForModule(moduleName);
            symbols = symbols.filter(s => s.name === word);
        } else {
            // Unqualified reference - search all symbols
            symbols = await this.symbolProvider.searchSymbols(word);
            symbols = symbols.filter(s => s.name === word);
        }

        if (symbols.length === 0) {
            return undefined;
        }

        // Create hover content
        const contents = new vscode.MarkdownString();

        // If multiple symbols with same name, show all
        for (let i = 0; i < symbols.length; i++) {
            const symbol = symbols[i];

            if (i > 0) {
                contents.appendMarkdown('\n\n---\n\n');
            }

            // Add symbol signature
            if (symbol.arity && symbol.arity > 0) {
                const params = Array(symbol.arity).fill('_').join(', ');
                contents.appendCodeblock(`${symbol.name}(${params})`, 'tlaplus');
            } else {
                contents.appendCodeblock(symbol.name, 'tlaplus');
            }

            // Add module information
            contents.appendMarkdown(`\n\n**Module:** ${symbol.module}\n\n`);

            // Add symbol kind
            const kindName = this.getSymbolKindName(symbol.kind);
            contents.appendMarkdown(`**Type:** ${kindName}\n\n`);

            // Add documentation if available
            if (symbol.documentation) {
                contents.appendMarkdown(symbol.documentation);
            }

            // Add usage example for common operators
            const example = this.getUsageExample(symbol.name, symbol.module);
            if (example) {
                contents.appendMarkdown('\n\n**Example:**\n');
                contents.appendCodeblock(example, 'tlaplus');
            }
        }

        return new vscode.Hover(contents, wordRange);
    }

    /**
     * Gets a human-readable name for a symbol kind.
     */
    private getSymbolKindName(kind: vscode.SymbolKind): string {
        switch (kind) {
            case vscode.SymbolKind.Function:
                return 'Operator';
            case vscode.SymbolKind.Constant:
                return 'Constant';
            case vscode.SymbolKind.Variable:
                return 'Variable';
            default:
                return 'Symbol';
        }
    }

    /**
     * Gets usage examples for well-known operators.
     */
    private getUsageExample(operatorName: string, moduleName: string): string | undefined {
        const examples: Record<string, string> = {
            // Sequences module
            'Append': 'Append(<<1, 2, 3>>, 4) = <<1, 2, 3, 4>>',
            'Head': 'Head(<<1, 2, 3>>) = 1',
            'Tail': 'Tail(<<1, 2, 3>>) = <<2, 3>>',
            'Len': 'Len(<<1, 2, 3>>) = 3',
            'SubSeq': 'SubSeq(<<1, 2, 3, 4>>, 2, 3) = <<2, 3>>',
            'SelectSeq': 'SelectSeq(<<1, 2, 3, 4>>, LAMBDA x: x > 2) = <<3, 4>>',

            // FiniteSets module
            'Cardinality': 'Cardinality({1, 2, 3}) = 3',
            'IsFiniteSet': 'IsFiniteSet({1, 2, 3}) = TRUE',

            // Integers module
            'Int': '42 \\in Int',
            'Nat': '5 \\in Nat',

            // Bags module
            'BagToSet': 'BagToSet(<<1, 2, 2, 3>>) = {1, 2, 3}',
            'SetToBag': 'SetToBag({1, 2, 3}) = <<1, 2, 3>>',
            'BagIn': 'BagIn(2, <<1, 2, 2, 3>>)',
            'EmptyBag': '<<1, 2>> (+) EmptyBag = <<1, 2>>',

            // TLC module
            'Print': 'Print("Debug message", value)',
            'PrintT': 'PrintT("Debug message")',
            'Assert': 'Assert(x > 0, "x must be positive")',
            'JavaTime': 'JavaTime',
            'TLCGet': 'TLCGet("stats")',
            'TLCSet': 'TLCSet("exit", TRUE)',

            // Randomization module
            'RandomElement': 'RandomElement({1, 2, 3, 4, 5})',

            // Json module
            'ToJson': 'ToJson([a |-> 1, b |-> "hello"])',
            'ToJsonArray': 'ToJsonArray(<<1, 2, 3>>)',
            'ToJsonObject': 'ToJsonObject([a |-> 1, b |-> 2])',

            // RealTime module
            'RTnow': 'RTnow',
            'RTBound': 'RTBound(op, delta)'
        };

        return examples[operatorName];
    }
}