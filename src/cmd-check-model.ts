import * as vscode from 'vscode';
import path = require('path');
import * as tools from './tla2tools';

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
    const javaPath = tools.buildJavaPath();
    if (!javaPath) {
        return;
    }
    const toolsArgs = ['-XX:+UseParallelGC', '-jar', tools.toolsJarPath, fileUri.fsPath];
    let workDir = path.dirname(fileUri.fsPath);
    return tools.executeJavaProcess(javaPath, toolsArgs, workDir)
            .then(res => {
                console.log('Check model ERR: ' + res.err);
                console.log('---- Check model STDOUT ----\n' + res.stdout);
                console.log('---- Check model STDERR ----\n' + res.stderr);            
            });
}
