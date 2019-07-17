import * as vscode from 'vscode';
import { runTool } from '../tla2tools';
import { TLCModelCheckerStdoutParser, ModelCheckResult, CheckStatus } from '../parsers/modelChecker';
import { revealCheckResultView, updateCheckResultView } from '../checkResultView';

// This class helps to keep view refresh frequency moderately low.
// We don't want to update view on every TLC message.
class UpdateInfo {
    static readonly TIMEOUT = 500;
    timer: NodeJS.Timer | undefined = undefined;
    first: boolean = true;
}

/**
 * Runs TLC on a TLA+ specification.
 */
export function checkModel(diagnostic: vscode.DiagnosticCollection) {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ model to check');
        return;
    }
    if (editor.document.languageId !== 'tlaplus') {
        vscode.window.showWarningMessage('File in the active editor is not a TLA+ file, it cannot be checked as a model');
        return;
    }
    doCheckModel(editor.document.uri, diagnostic);
}

async function doCheckModel(fileUri: vscode.Uri, diagnostic: vscode.DiagnosticCollection) {
    try {
        const proc = runTool('tlc2.TLC', fileUri.fsPath, ['-modelcheck', '-tool']);
        revealCheckResultView(null);
        const updInfo = new UpdateInfo();
        const viewUpdater = (checkResult: ModelCheckResult) => {
            if (updInfo.timer) {
                clearTimeout(updInfo.timer);
            }
            let timeout = UpdateInfo.TIMEOUT;
            if (updInfo.first && checkResult.getStatus() !== CheckStatus.NotStarted) {
                updInfo.first = false;
                timeout = 0;
            }
            updInfo.timer = setTimeout(() => {
                updateCheckResultView(checkResult);
                updInfo.timer = undefined;
            }, timeout);
        };
        const stdoutParser = new TLCModelCheckerStdoutParser(proc.stdout, fileUri.fsPath, viewUpdater);
        const messages = await stdoutParser.readAll();    
        messages.apply(diagnostic);
    } catch (e) {
        vscode.window.showErrorMessage(e.message);
    }
}
