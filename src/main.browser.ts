import * as vscode from 'vscode';
import { CfgCompletionItemProvider } from './completions/cfgCompletions';
import { TlaCompletionItemProvider } from './completions/tlaCompletions';
import { TlaDefinitionsProvider, TlaDeclarationsProvider } from './declarations/tlaDeclarations';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG } from './common';
import { CfgOnTypeFormattingEditProvider } from './formatters/cfg';
import { TlaOnTypeFormattingEditProvider } from './formatters/tla';
import { TlaDocumentSymbolsProvider } from './symbols/tlaSymbols';
import { createExtensionRuntime } from './runtime/extensionRuntime';

const TLAPLUS_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS };
const TLAPLUS_CFG_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS_CFG };

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    const diagnosticCollection = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
    const runtime = createExtensionRuntime(diagnosticCollection);

    context.subscriptions.push(
        diagnosticCollection,
        vscode.languages.registerOnTypeFormattingEditProvider(TLAPLUS_FILE_SELECTOR, new TlaOnTypeFormattingEditProvider(), '\n', 'd', 'e', 'f', 'r'),
        vscode.languages.registerOnTypeFormattingEditProvider(TLAPLUS_CFG_FILE_SELECTOR, new CfgOnTypeFormattingEditProvider(), '\n'),
        vscode.languages.registerDocumentSymbolProvider(TLAPLUS_FILE_SELECTOR, new TlaDocumentSymbolsProvider(runtime.semanticService), { label: 'TLA+' }),
        vscode.languages.registerCompletionItemProvider(TLAPLUS_FILE_SELECTOR, new TlaCompletionItemProvider(runtime.semanticService)),
        vscode.languages.registerCompletionItemProvider(TLAPLUS_CFG_FILE_SELECTOR, new CfgCompletionItemProvider()),
        vscode.languages.registerDeclarationProvider(TLAPLUS_FILE_SELECTOR, new TlaDeclarationsProvider(runtime.semanticService)),
        vscode.languages.registerDefinitionProvider(TLAPLUS_FILE_SELECTOR, new TlaDefinitionsProvider(runtime.semanticService)),
    );
}
