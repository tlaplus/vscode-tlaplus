import * as vscode from 'vscode';
import * as path from 'path';
import { replaceExtension, deleteDir, readFileLines, exists } from '../common';
import { SpecFiles, getEditorIfCanRunTlc, doCheckModel } from './checkModel';
import { createCustomModel } from './customModel';

export const CMD_EVALUATE_SELECTION = 'tlaplus.evaluateSelection';

const EXPR_MARKER = '$!@$!@$!@$!@$!';

let lastEvaluatedExpression: string | undefined;

/**
 * Evaluates the expression, currently selected in the active editor.
 */
export async function evaluateSelection(diagnostic: vscode.DiagnosticCollection, extContext: vscode.ExtensionContext) {
    const editor = getEditorIfCanRunTlc(extContext);
    if (!editor) {
        return;
    }
    const selRange = new vscode.Range(editor.selection.start, editor.selection.end);
    const selText = editor.document.getText(selRange);
    doEvaluateExpression(editor.document.uri.fsPath, selText, diagnostic, extContext);
}

/**
 * Asks the user to enter an expression and evalutes it in the context of the specification from the active editor.
 */
export async function evaluateExpression(diagnostic: vscode.DiagnosticCollection, extContext: vscode.ExtensionContext) {
    const editor = getEditorIfCanRunTlc(extContext);
    if (!editor) {
        return;
    }
    vscode.window.showInputBox({
        value: lastEvaluatedExpression,
        prompt: 'Enter a TLA+ expression to evaluate',
        ignoreFocusOut: true
    }).then((expr) => {
        if (!expr) {
            return;
        }
        lastEvaluatedExpression = expr;
        doEvaluateExpression(editor.document.uri.fsPath, expr, diagnostic, extContext);
    });
}

async function doEvaluateExpression(
    tlaFilePath: string,
    expr: string,
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
) {
    const eExpr = expr.trim();
    if (eExpr === '') {
        vscode.window.showWarningMessage('Nothing to evaluate.');
        return;
    }
    const cfgFilePath = replaceExtension(tlaFilePath, 'cfg');
    const cfgExists = await exists(cfgFilePath);
    const constants = cfgExists ? await extractConstants(cfgFilePath) : [];
    const num = (new Date().getTime());
    const model = await createCustomModel(
        tlaFilePath, [
            `E_${num} ==`,
            expr,
            `ASSUME PrintT(<<"${EXPR_MARKER}", E_${num}>>)`,
            `VARIABLES v_${num}`,
            `Init_${num} == FALSE /\\ v_${num} = 0`,
            `Next_${num} == FALSE /\\ v_${num}' = v_${num}`
        ], constants.concat([
            `INIT Init_${num}`,
            `NEXT Next_${num}`
        ])
    );
    if (!model) {
        return;
    }
    const specFiles = new SpecFiles(
        path.join(model.dirPath, model.tlaFileName),
        path.join(model.dirPath, model.cfgFileName)
    );
    doCheckModel(specFiles, extContext, diagnostic);
    // deleteDir(model.dirPath);
}

async function extractConstants(cfgFilePath: string): Promise<string[]> {
    const lines = await readFileLines(cfgFilePath);
    const constants = [];
    let c = false;
    for (const line of lines) {
        if (/^\s*CONSTANT(S)?\b/g.test(line)) {
            c = true;
        } else if (/^\s*(SPECIFICATION|INVARIANT(S)?|PROPERT(Y|IES)|INIT|NEXT|SYMMETRY|CONSTRAINT(S)?|ACTION_CONSTRAINT(S)?|VIEW)\b/g.test(line)) {
            c = false;
        }
        if (c && line !== '') {
            constants.push(line);
        }
    }
    return constants;
}
