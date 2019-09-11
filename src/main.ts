import * as vscode from 'vscode';
import { CMD_CHECK_MODEL_RUN, CMD_CHECK_MODEL_STOP, CMD_CHECK_MODEL_DISPLAY, CMD_SHOW_TLC_OUTPUT,
    CMD_CHECK_MODEL_CUSTOM_RUN, checkModel, displayModelChecking, stopModelChecking,
    showTlcOutput, checkModelCustom} from './commands/checkModel';
import { parseModule, CMD_PARSE_MODULE } from './commands/parseModule';
import { visualizeTlcOutput, CMD_VISUALIZE_TLC_OUTPUT } from './commands/visualizeOutput';
import { TlaOnTypeFormattingEditProvider } from './formatters/tla';
import { CfgOnTypeFormattingEditProvider } from './formatters/cfg';
import { TlaCodeActionProvider } from './actions';
import { TlaDocumentSymbolsProvider } from './symbols/tlaSymbols';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG } from './common';

// Holds all the error messages
let diagnostic: vscode.DiagnosticCollection;

/**
 * Extension entry point.
 */
export function activate(context: vscode.ExtensionContext) {
    diagnostic = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
    context.subscriptions.push(
        vscode.commands.registerCommand(
            CMD_PARSE_MODULE,
            () => parseModule(diagnostic)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_RUN,
            () => checkModel(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_CUSTOM_RUN,
            () => checkModelCustom(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_SHOW_TLC_OUTPUT,
            () => showTlcOutput()),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_STOP,
            () => stopModelChecking()),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_DISPLAY,
            () => displayModelChecking(context)),
        vscode.commands.registerCommand(
            CMD_VISUALIZE_TLC_OUTPUT,
            () => visualizeTlcOutput(context)),
        vscode.languages.registerCodeActionsProvider(
            { scheme: 'file', language: LANG_TLAPLUS },
            new TlaCodeActionProvider(),
            { providedCodeActionKinds: [ vscode.CodeActionKind.Source ] }),
        vscode.languages.registerOnTypeFormattingEditProvider(
            { scheme: 'file', language: LANG_TLAPLUS },
            new TlaOnTypeFormattingEditProvider(),
            '\n', 'd', 'e', 'f', 'r'),
        vscode.languages.registerOnTypeFormattingEditProvider(
            { scheme: 'file', language: LANG_TLAPLUS_CFG },
            new CfgOnTypeFormattingEditProvider(),
            '\n'),
        vscode.languages.registerDocumentSymbolProvider(
            { scheme: 'file', language: LANG_TLAPLUS },
            new TlaDocumentSymbolsProvider(),
            { label: 'TLA+' }
        )
    );
}

export function deactivate() {}
