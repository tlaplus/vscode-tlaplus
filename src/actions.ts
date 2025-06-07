import * as vscode from 'vscode';
import { CMD_PARSE_MODULE } from './commands/parseModule';
import { TLAPLUS_DEBUG_LAUNCH_SMOKE } from './debugger/debugging';

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

    smokeTestModel: vscode.CodeAction = {
        kind: vscode.CodeActionKind.Source,
        title: 'Smoke test model',
        command: {
            title: 'Smoke test model',
            command: TLAPLUS_DEBUG_LAUNCH_SMOKE
        }
    };

    provideCodeActions(
        document: vscode.TextDocument,
        range: vscode.Range | vscode.Selection,
        context: vscode.CodeActionContext,
        token: vscode.CancellationToken
    ): vscode.ProviderResult<(vscode.Command | vscode.CodeAction)[]> {
        const actions: (vscode.Command | vscode.CodeAction)[] = [
            this.actParseModule,
            this.smokeTestModel
        ];

        // Check if cursor is on a line with "vars =="
        const line = document.lineAt(range.start.line);
        const lineText = line.text;

        if (lineText.match(/^\s*vars\s*==/)) {
            const updateVarsAction = new vscode.CodeAction(
                'Update vars tuple',
                vscode.CodeActionKind.RefactorRewrite
            );
            updateVarsAction.command = {
                command: 'tlaplus.refactor.update_vars',
                title: 'Update vars tuple'
            };
            actions.push(updateVarsAction);
        }

        return actions;
    }
}
