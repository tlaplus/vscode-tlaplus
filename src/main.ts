import * as vscode from 'vscode';
import {checkModel} from './cmd-check-model';
import {parseModule} from './cmd-parse-module';


// Holds all the error messages
let diagnostic: vscode.DiagnosticCollection;

/**
 * Extension entry point.
 */
export function activate(context: vscode.ExtensionContext) {
    diagnostic = vscode.languages.createDiagnosticCollection('tlaplus');
    let cmdParse = vscode.commands.registerCommand('tlaplus.parse', () => parseModule(diagnostic));
    let cmdCheckModel = vscode.commands.registerCommand('tlaplus.model.check', () => checkModel(diagnostic));
    context.subscriptions.push(cmdParse);
    context.subscriptions.push(cmdCheckModel);
}

export function deactivate() {}
