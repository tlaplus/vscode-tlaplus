import * as vscode from 'vscode';
import * as assert from 'assert';
import { parseDocInfo, replaceDocContents, applyDocEdits } from '../document';

export const OPT_4_SPACES: vscode.FormattingOptions = { insertSpaces: true, tabSize: 4 };
export const OPT_2_SPACES: vscode.FormattingOptions = { insertSpaces: true, tabSize: 2 };
export const OPT_7_SPACES: vscode.FormattingOptions = { insertSpaces: true, tabSize: 7 };
export const OPT_TABS: vscode.FormattingOptions = { insertSpaces: false, tabSize: 4 };

export async function assertOnTypeFormatting(
    formatter: vscode.OnTypeFormattingEditProvider,
    doc: vscode.TextDocument,
    docLines: string[],
    expectLines: string[],
    options: vscode.FormattingOptions
): Promise<void> {
    const docInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, docInfo.lines.join('\n'));
    const tokenSrc = new vscode.CancellationTokenSource();
    const edits = await formatter.provideOnTypeFormattingEdits(
        doc,
        docInfo.position,
        docInfo.char,
        options,
        tokenSrc.token
    );
    await applyDocEdits(doc.uri, edits);
    assert.deepEqual(doc.getText().split('\n'), expectLines);
    return undefined;
}
