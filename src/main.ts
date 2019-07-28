import * as vscode from 'vscode';
import { checkModel, CMD_CHECK_MODEL, CMD_CHECK_MODEL_DISPLAY, displayModelChecking } from './commands/checkModel';
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
    const cmdCheckModel = vscode.commands.registerCommand(
        CMD_CHECK_MODEL,
        () => checkModel(diagnostic, context));
    const cmdCheckModelDisplay = vscode.commands.registerCommand(
        CMD_CHECK_MODEL_DISPLAY,
        () => displayModelChecking(context));
    context.subscriptions.push(cmdParse);
    context.subscriptions.push(cmdCheckModel);
    context.subscriptions.push(cmdCheckModelDisplay);
}

export function deactivate() {}
