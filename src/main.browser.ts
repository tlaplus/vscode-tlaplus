import * as vscode from 'vscode';

import { CfgCompletionItemProvider } from './completions/cfgCompletions';
import { TlaCompletionItemProvider } from './completions/tlaCompletions';
import { TlaDeclarationsProvider, TlaDefinitionsProvider } from './declarations/tlaDeclarations';
import { CfgOnTypeFormattingEditProvider } from './formatters/cfg';
import { TlaOnTypeFormattingEditProvider } from './formatters/tla';
import { TlaDocumentInfos } from './model/documentInfo';
import { TlaDocumentSymbolsProvider } from './symbols/tlaSymbols';
import { ModuleSymbolProvider } from './symbols/moduleSymbolProvider';

const LANG_TLAPLUS = 'tlaplus';
const LANG_TLAPLUS_CFG = 'tlaplus_cfg';
const tlaDocInfos = new TlaDocumentInfos();
const moduleSymbolProvider = new ModuleSymbolProvider();

/**
 * Extension entry point.
 */
export function activate(context: vscode.ExtensionContext): void {
    context.subscriptions.push(
        vscode.languages.registerOnTypeFormattingEditProvider(
            LANG_TLAPLUS,
            new TlaOnTypeFormattingEditProvider(),
            '\n', 'd', 'e', 'f', 'r'),
        vscode.languages.registerOnTypeFormattingEditProvider(
            LANG_TLAPLUS_CFG,
            new CfgOnTypeFormattingEditProvider(),
            '\n'),
        vscode.languages.registerDocumentSymbolProvider(
            LANG_TLAPLUS,
            new TlaDocumentSymbolsProvider(tlaDocInfos),
            { label: 'TLA+' }),
        vscode.languages.registerCompletionItemProvider(
            LANG_TLAPLUS,
            new TlaCompletionItemProvider(tlaDocInfos, moduleSymbolProvider)),
        vscode.languages.registerCompletionItemProvider(
            LANG_TLAPLUS_CFG,
            new CfgCompletionItemProvider()),
        vscode.languages.registerDeclarationProvider(
            LANG_TLAPLUS,
            new TlaDeclarationsProvider(tlaDocInfos)),
        vscode.languages.registerDefinitionProvider(
            LANG_TLAPLUS,
            new TlaDefinitionsProvider(tlaDocInfos)
        )
    );
}
