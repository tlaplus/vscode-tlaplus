import * as vscode from 'vscode';
import * as path from 'path';
import { replaceExtension, deleteDir, readFile, exists } from '../common';
import { getEditorIfCanRunTlc, doCheckModel } from './checkModel';
import { createCustomModel } from './customModel';
import { ToolOutputChannel } from '../outputChannels';
import { ModelCheckResult, CheckState, SequenceValue, Value, OutputLine, SpecFiles } from '../model/check';
import { parseVariableValue } from '../parsers/tlcValues';

export const CMD_EVALUATE_SELECTION = 'tlaplus.evaluateSelection';
export const CMD_EVALUATE_EXPRESSION = 'tlaplus.evaluateExpression';

const EXPR_MARKER = '$!@$!@$!@$!@$!';

let lastEvaluatedExpression: string | undefined;
const outChannel = new ToolOutputChannel('TLA+ evaluation');

/**
 * Evaluates the expression, currently selected in the active editor.
 */
export async function evaluateSelection(
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
): Promise<void> {
    const editorResult = getEditorIfCanRunTlc(extContext);
    if (editorResult.isErr()) {
        vscode.window.showErrorMessage(editorResult.error.message);
        return;
    }
    const editor = editorResult.value;

    const selRange = new vscode.Range(editor.selection.start, editor.selection.end);
    const selText = editor.document.getText(selRange);
    doEvaluateExpression(editor, selText, diagnostic, extContext);
}

/**
 * Asks the user to enter an expression and evalutes it in the context of the specification from the active editor.
 */
export async function evaluateExpression(
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
): Promise<void> {
    const editorResult = getEditorIfCanRunTlc(extContext);
    if (editorResult.isErr()) {
        vscode.window.showErrorMessage(editorResult.error.message);
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
        doEvaluateExpression(editorResult.value, expr, diagnostic, extContext);
    });
}

async function doEvaluateExpression(
    editor: vscode.TextEditor,
    expr: string,
    diagnostic: vscode.DiagnosticCollection,
    extContext: vscode.ExtensionContext
) {
    const eExpr = expr.trim();
    if (eExpr === '') {
        vscode.window.showWarningMessage('Nothing to evaluate.');
        return;
    }
    await editor.document.save();
    const tlaFilePath = editor.document.uri.fsPath;
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
    outChannel.clear();
    outChannel.appendLine(`Evaluating constant expression:\n${expr}\n`);
    outChannel.revealWindow();
    const checkResult = await doCheckModel(specFiles, false, extContext, diagnostic, false);
    displayResult(checkResult);
    deleteDir(model.dirPath);
}

async function extractConstants(cfgFilePath: string): Promise<string[]> {
    const lines = (await readFile(cfgFilePath)).split('\n');
    const constants = [];
    let constLine = false;
    // eslint-disable-next-line max-len
    const wordsRegex = /^\s*(SPECIFICATION|INVARIANT(S)?|PROPERT(Y|IES)|INIT|NEXT|SYMMETRY|CONSTRAINT(S)?|ACTION_CONSTRAINT(S)?|VIEW|CHECK_DEADLOCK|POSTCONDITION|ALIAS)\b/g;
    for (const line of lines) {
        if (/^\s*CONSTANT(S)?\b/g.test(line)) {
            constLine = true;
        } else if (wordsRegex.test(line)) {
            constLine = false;
        }
        if (constLine && line !== '') {
            constants.push(line);
        }
    }
    return constants;
}

function displayResult(checkResult: ModelCheckResult | undefined) {
    if (!checkResult) {
        outChannel.appendLine('Error evaluating expression');
        return;
    }
    if (checkResult.state !== CheckState.Success) {
        outChannel.appendLine('Error evaluating expression:');
        checkResult.errors.forEach((err) => {
            err.lines.forEach((line) => outChannel.appendLine(line.toString()));
        });
        return;
    }
    const valLines = extractCalculatedExpressionLines(checkResult.outputLines);
    let exprVal;
    if (valLines.length > 0) {
        const val = parseVariableValue('', valLines);
        exprVal = extractCalculatedExpressionValue(val);
    }
    outChannel.appendLine(exprVal || 'Error: Expression value output not found.');
    outChannel.revealWindow();  // VS Code sometimes swithes the window to TLC output, so we need to get it back
}

function extractCalculatedExpressionLines(outLines: OutputLine[]): string[] {
    const lines = [];
    for (const outLine of outLines) {
        const text = outLine.text;
        if (lines.length > 0 || (lines.length === 0 && text.indexOf(EXPR_MARKER) >= 0)) {
            for (let i = 0; i < outLine.count; i++) {
                lines.push(text);
            }
        }
        if (lines.length > 0 && text.endsWith('>>')) {
            break;
        }
    }
    return lines;
}

function extractCalculatedExpressionValue(val: Value): string | undefined {
    if (!(val instanceof SequenceValue)) {
        return undefined;
    }
    if (val.items.length !== 2) {
        return undefined;
    }
    return val.items[0].str === `"${EXPR_MARKER}"` ? val.items[1].str : undefined;
}
