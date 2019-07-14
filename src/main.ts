import * as vscode from 'vscode';
import {parseModule} from './tla2tools';

let diagnostic: vscode.DiagnosticCollection;

export function activate(context: vscode.ExtensionContext) {
    console.log('TLA+ activated');

    diagnostic = vscode.languages.createDiagnosticCollection('tlaplus');
	let cmdTranspile = vscode.commands.registerCommand('tlaplus.parse', () => parseModule(diagnostic));
	context.subscriptions.push(cmdTranspile);
}

export function deactivate() {}