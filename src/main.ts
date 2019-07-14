import * as vscode from 'vscode';
import {parseModule, checkModel} from './tla2tools';

let diagnostic: vscode.DiagnosticCollection;

export function activate(context: vscode.ExtensionContext) {
    console.log('TLA+ activated');

    diagnostic = vscode.languages.createDiagnosticCollection('tlaplus');
	let cmdParse = vscode.commands.registerCommand('tlaplus.parse', () => parseModule(diagnostic));
	let cmdCheckModel = vscode.commands.registerCommand('tlaplus.model.check', () => checkModel(diagnostic));
	context.subscriptions.push(cmdParse);
	context.subscriptions.push(cmdCheckModel);
}

export function deactivate() {}