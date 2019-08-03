import * as vscode from 'vscode';
import { CMD_CHECK_MODEL_RUN, CMD_CHECK_MODEL_STOP, CMD_CHECK_MODEL_DISPLAY,
    checkModel, displayModelChecking, stopModelChecking } from './commands/checkModel';
import { parseModule, CMD_PARSE_MODULE } from './commands/parseModule';

// Holds all the error messages
let diagnostic: vscode.DiagnosticCollection;

/**
 * Extension entry point.
 */
export function activate(context: vscode.ExtensionContext) {
    diagnostic = vscode.languages.createDiagnosticCollection('tlaplus');
    const cmdParse = vscode.commands.registerCommand(
        CMD_PARSE_MODULE,
        () => parseModule(diagnostic));
    const cmdCheckModelRun = vscode.commands.registerCommand(
        CMD_CHECK_MODEL_RUN,
        () => checkModel(diagnostic, context));
    const cmdCheckModelStop = vscode.commands.registerCommand(
        CMD_CHECK_MODEL_STOP,
        () => stopModelChecking());
    const cmdCheckModelDisplay = vscode.commands.registerCommand(
        CMD_CHECK_MODEL_DISPLAY,
        () => displayModelChecking(context));
    context.subscriptions.push(cmdParse);
    context.subscriptions.push(cmdCheckModelRun);
    context.subscriptions.push(cmdCheckModelStop);
    context.subscriptions.push(cmdCheckModelDisplay);
}

export function deactivate() {}
