import * as vscode from 'vscode';
import { CMD_PARSE_MODULE } from './commands/parseModule';

/**
 * Provides actions for .tla files.
 */
export class TlaCodeActionProvider implements vscode.CodeActionProvider {
    actParseModule: vscode.CodeAction = {
        kind: vscode.CodeActionKind.Source,
        title: 'Parse module',
        command: {
            title: 'Parse module',
            command: CMD_PARSE_MODULE
        }
    };

    provideCodeActions(
        document: vscode.TextDocument,
        range: vscode.Range | vscode.Selection,
        context: vscode.CodeActionContext,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<(vscode.Command | vscode.CodeAction)[]> {
        return [ this.actParseModule ];
    }
}
