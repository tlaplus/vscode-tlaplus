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

        // Check if this is a module name in an EXTENDS statement
        const line = document.lineAt(position.line).text;
        const beforeWord = line.substring(0, wordRange.start.character);

        // Check if we're in an EXTENDS statement
        let inExtendsStatement = false;
        if (/EXTENDS\s*$/.test(beforeWord) || /EXTENDS\s+[\w\s,]*$/.test(beforeWord)) {
            inExtendsStatement = true;
        } else {
            // Check if we're on a continuation line of an EXTENDS statement
            for (let i = position.line - 1; i >= 0; i--) {
                const prevLine = document.lineAt(i).text;
                if (/EXTENDS\s+[\w\s,]*$/.test(prevLine)) {
                    // Check if there's no other statement between EXTENDS and current position
                    let hasOtherStatement = false;
                    for (let j = i + 1; j < position.line; j++) {
                        const checkLine = document.lineAt(j).text.trim();
                        if (checkLine && !checkLine.startsWith(',') && !/^[\w\s,]+$/.test(checkLine)) {
                            hasOtherStatement = true;
                            break;
                        }
                    }
                    if (!hasOtherStatement) {
                        inExtendsStatement = true;
                    }
                    break;
                }
                // Stop if we hit another statement
                if (prevLine.trim() && !/^[\w\s,]+$/.test(prevLine.trim())) {
                    break;
                }
            }
        }

        if (inExtendsStatement) {
            // Provide hover for module name
            return this.provideModuleHover(word, wordRange);
        }

        // Check if this is a qualified reference (Module!Symbol)
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
     * Provides hover information for module names in EXTENDS statements.
     */
    private async provideModuleHover(moduleName: string, wordRange: vscode.Range): Promise<vscode.Hover | undefined> {
        const contents = new vscode.MarkdownString();

        // Add module name header
        contents.appendCodeblock(moduleName, 'tlaplus');
        contents.appendMarkdown('\n\n');

        // Get symbols exported by this module
        const symbols = await this.symbolProvider.getSymbolsForModule(moduleName);

        if (symbols.length > 0) {
            // Group symbols by kind
            const operators = symbols.filter(s => s.kind === vscode.SymbolKind.Function);
            const constants = symbols.filter(s => s.kind === vscode.SymbolKind.Constant);
            const variables = symbols.filter(s => s.kind === vscode.SymbolKind.Variable);
            const others = symbols.filter(s =>
                s.kind !== vscode.SymbolKind.Function &&
                s.kind !== vscode.SymbolKind.Constant &&
                s.kind !== vscode.SymbolKind.Variable
            );


            // List exported symbols
            contents.appendMarkdown(`**Exports ${symbols.length} symbols:**\n\n`);

            if (operators.length > 0) {
                contents.appendMarkdown(`**Operators (${operators.length}):**\n`);
                const operatorNames = operators.slice(0, 10).map(o => {
                    if (o.arity && o.arity > 0) {
                        return `${o.name}/${o.arity}`;
                    }
                    return o.name;
                });
                contents.appendMarkdown(`\`${operatorNames.join('`, `')}\``);
                if (operators.length > 10) {
                    contents.appendMarkdown(` and ${operators.length - 10} more...`);
                }
                contents.appendMarkdown('\n\n');
            }

            if (constants.length > 0) {
                contents.appendMarkdown(`**Constants (${constants.length}):**\n`);
                const constantNames = constants.slice(0, 10).map(c => c.name);
                contents.appendMarkdown(`\`${constantNames.join('`, `')}\``);
                if (constants.length > 10) {
                    contents.appendMarkdown(` and ${constants.length - 10} more...`);
                }
                contents.appendMarkdown('\n\n');
            }

            if (variables.length > 0) {
                contents.appendMarkdown(`**Variables (${variables.length}):**\n`);
                const variableNames = variables.slice(0, 10).map(v => v.name);
                contents.appendMarkdown(`\`${variableNames.join('`, `')}\``);
                if (variables.length > 10) {
                    contents.appendMarkdown(` and ${variables.length - 10} more...`);
                }
                contents.appendMarkdown('\n\n');
            }

            if (others.length > 0) {
                contents.appendMarkdown(`**Other symbols (${others.length}):**\n`);
                const otherNames = others.slice(0, 10).map(o => o.name);
                contents.appendMarkdown(`\`${otherNames.join('`, `')}\``);
                if (others.length > 10) {
                    contents.appendMarkdown(` and ${others.length - 10} more...`);
                }
                contents.appendMarkdown('\n\n');
            }
        } else {
            contents.appendMarkdown('**Type:** Module\n\n');
            contents.appendMarkdown('*No symbols found in registry. Module may need to be parsed.*\n');
        }

        return new vscode.Hover(contents, wordRange);
    }

}