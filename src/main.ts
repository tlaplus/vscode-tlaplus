import * as vscode from 'vscode';
import { CMD_CHECK_MODEL_RUN, CMD_CHECK_MODEL_STOP, CMD_CHECK_MODEL_DISPLAY, CMD_SHOW_TLC_OUTPUT,
    CMD_CHECK_MODEL_CUSTOM_RUN, checkModel, displayModelChecking, stopModelChecking,
    showTlcOutput, checkModelCustom} from './commands/checkModel';
import { parseModule, CMD_PARSE_MODULE } from './commands/parseModule';
import { visualizeTlcOutput, CMD_VISUALIZE_TLC_OUTPUT } from './commands/visualizeOutput';
import { TlaOnTypeFormattingEditProvider } from './formatting';
import { TlaCodeActionProvider } from './actions';

// Holds all the error messages
let diagnostic: vscode.DiagnosticCollection;

/**
 * Extension entry point.
 */
export function activate(context: vscode.ExtensionContext) {
    diagnostic = vscode.languages.createDiagnosticCollection('tlaplus');
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
            { scheme: 'file', language: 'tlaplus' },
            new TlaCodeActionProvider(),
            { providedCodeActionKinds: [ vscode.CodeActionKind.Source ] }),
        vscode.languages.registerOnTypeFormattingEditProvider(
            { scheme: 'file', language: 'tlaplus' },
            new TlaOnTypeFormattingEditProvider(),
            '\n', 'd', 'e', 'f', 'r')
    );
}

export function deactivate() {}
