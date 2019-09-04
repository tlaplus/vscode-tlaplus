import * as vscode from 'vscode';
import * as assert from 'assert';
import { TlaOnTypeFormattingEditProvider } from '../../src/formatting';

const ZERO_POSITION = new vscode.Position(0, 0);
const OPT_4_SPACES: vscode.FormattingOptions = { insertSpaces: true, tabSize: 4 };

suite('On Type Formatting Test Suite', () => {
    let doc: vscode.TextDocument;

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({ language: 'tlaplus' });
    });

    suiteTeardown(async () => {
        await vscode.window.showTextDocument(doc, {preview: true, preserveFocus: false});
        return vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Indents begin-block body', () => {
        return assertOnTypeFormatting(doc, [
                'begin',
                '{enter}(**)'
            ], [
                'begin',
                '    (**)'
            ]
        );
    });

    test('Indents define-block body', () => {
        return assertOnTypeFormatting(doc, [
                'define',
                '{enter}(**)'
            ], [
                'define',
                '    (**)'
            ]
        );
    });

    test('Indents define-block closing', () => {
        return assertOnTypeFormatting(doc, [
                'define',
                '    FOO == 10',
                '    en{d}',
            ], [
                'define',
                '    FOO == 10',
                'end',
            ]
        );
    });

    test('Indents macro-block body', () => {
        return assertOnTypeFormatting(doc, [
                'macro foo(x) begin',
                '{enter}(**)'
            ], [
                'macro foo(x) begin',
                '    (**)'
            ]
        );
    });

    test('Indents macro-block closing', () => {
        return assertOnTypeFormatting(doc, [
                'macro foo(x) begin',
                '     skip;',
                '     en{d} macro;'
            ], [
                'macro foo(x) begin',
                '     skip;',
                'end macro;'
            ]
        );
    });

    test('Indents procedure-block body', () => {
        return assertOnTypeFormatting(doc, [
                'procedure foo(x) begin',
                '{enter}(**)'
            ], [
                'procedure foo(x) begin',
                '    (**)'
            ]
        );
    });

    test('Indents procedure-block closing', () => {
        return assertOnTypeFormatting(doc, [
                'procedure foo(x) begin',
                '    Ret: return;',
                '    en{d}'
            ], [
                'procedure foo(x) begin',
                '    Ret: return;',
                'end'
            ]
        );
    });

    test('Indents if-block body', () => {
        return assertOnTypeFormatting(doc, [
                '    if TRUE then',
                '    {enter}(**)'
            ], [
                '    if TRUE then',
                '        (**)'
            ]
        );
    });

    test('Indents else-line', () => {
        return assertOnTypeFormatting(doc, [
                '    if foo = bar then',
                '        skip;',
                '        els{e}'
            ], [
                '    if foo = bar then',
                '        skip;',
                '    else'
            ]
        );
    });

    test('Indents else-block body', () => {
        return assertOnTypeFormatting(doc, [
                '    if foo = bar then',
                '        skip;',
                '    else',
                '    {enter}(**)'
            ], [
                '    if foo = bar then',
                '        skip;',
                '    else',
                '        (**)'
            ]
        );
    });

    test('Indents elsif-line', () => {
        return assertOnTypeFormatting(doc, [
                '    if foo = bar then',
                '        skip;',
                '        elsi{f}'
            ], [
                '    if foo = bar then',
                '        skip;',
                '    elsif'
            ]
        );
    });

    test('Indents elsif-block body', () => {
        return assertOnTypeFormatting(doc, [
                '    if foo = bar then',
                '        skip;',
                '    elsif foo = bar-1 then',
                '    {enter}(**)'
            ], [
                '    if foo = bar then',
                '        skip;',
                '    elsif foo = bar-1 then',
                '        (**)'
            ]
        );
    });

    test('Indents if-block closing', () => {
        return assertOnTypeFormatting(doc, [
                '    if foo = bar then',
                '        skip;',
                '        en{d}',
            ], [
                '    if foo = bar then',
                '        skip;',
                '    end',
            ]
        );
    });

    test('Indents if-block closing after else', () => {
        return assertOnTypeFormatting(doc, [
                '    if foo = bar then',
                '        skip;',
                '    else',
                '        skip;',
                '        en{d}',
            ], [
                '    if foo = bar then',
                '        skip;',
                '    else',
                '        skip;',
                '    end',
            ]
        );
    });

    test('Indents if-block closing after elsif', () => {
        return assertOnTypeFormatting(doc, [
                '    if foo = bar then',
                '        skip;',
                '    elsif foo = 10 then',
                '        skip;',
                '        en{d}',
            ], [
                '    if foo = bar then',
                '        skip;',
                '    elsif foo = 10 then',
                '        skip;',
                '    end',
            ]
        );
    });

    test('Indents either-block body', () => {
        return assertOnTypeFormatting(doc, [
                '    either',
                '    {enter}(**)'
            ], [
                '    either',
                '        (**)'
            ]
        );
    });

    test('Indents or-line', () => {
        return assertOnTypeFormatting(doc, [
                '    either',
                '        foo := 1;',
                '        o{r}'
            ], [
                '    either',
                '        foo := 1;',
                '    or'
            ]
        );
    });

    test('Indents or-block body', () => {
        return assertOnTypeFormatting(doc, [
                '    either',
                '        foo := 1;',
                '    or',
                '    {enter}(**)'
            ], [
                '    either',
                '        foo := 1;',
                '    or',
                '        (**)'
            ]
        );
    });

    test('Indents either-block closing', () => {
        return assertOnTypeFormatting(doc, [
                '    either',
                '        skip;',
                '        en{d}'
            ], [
                '    either',
                '        skip;',
                '    end'
            ]
        );
    });

    test('Indents either-block closing after or', () => {
        return assertOnTypeFormatting(doc, [
                '    either',
                '        skip;',
                '    or',
                '        foo := 20;',
                '        en{d}'
            ], [
                '    either',
                '        skip;',
                '    or',
                '        foo := 20;',
                '    end'
            ]
        );
    });

    test('Indents while-block body', () => {
        return assertOnTypeFormatting(doc, [
                '    while a < b do',
                '    {enter}(**)'
            ], [
                '    while a < b do',
                '        (**)'
            ]
        );
    });

    test('Indents while-block closing', () => {
        return assertOnTypeFormatting(doc, [
                '    while a < b do',
                '        skip;',
                '        en{d}'
            ], [
                '    while a < b do',
                '        skip;',
                '    end'
            ]
        );
    });

    test('Indents with-block body', () => {
        return assertOnTypeFormatting(doc, [
                'with a = 100 do',
                '{enter}(**)'
            ], [
                'with a = 100 do',
                '    (**)'
            ]
        );
    });

    test('Indents with-block closing', () => {
        return assertOnTypeFormatting(doc, [
                '    with a = 100 do',
                '        skip;',
                '    en{d}'
            ], [
                '    with a = 100 do',
                '        skip;',
                '    end'
            ]
        );
    });

    test('Indents variables-block when it\'s empty', () => {
        return assertOnTypeFormatting(doc, [
            '    variables',
            '    {enter}'
        ], [
            '    variables',
            '        '
        ]);
    });

    test('Indents VARIABLES-block when it\'s empty', () => {
        return assertOnTypeFormatting(doc, [
            '    VARIABLES',
            '    {enter}'
        ], [
            '    VARIABLES',
            '        '
        ]);
    });

    test('Indents CONSTANTS-block when it\'s empty', () => {
        return assertOnTypeFormatting(doc, [
            '    CONSTANTS',
            '    {enter}'
        ], [
            '    CONSTANTS',
            '        '
        ]);
    });

    test('Indents label-blocks', () => {
        return assertOnTypeFormatting(doc, [
            '    LabelA:',
            '    {enter}'
        ], [
            '    LabelA:',
            '        '
        ]);
    });

    test('Indents definitions with AND', () => {
        return assertOnTypeFormatting(doc, [
            '  NewState == /\\ TRUE',
            '  {enter}'
        ], [
            '  NewState == /\\ TRUE',
            '              '
        ]);
    });

    test('Indents definitions with OR', () => {
        return assertOnTypeFormatting(doc, [
            '  NewState == \\/ Foo = Bar',
            '  {enter}'
        ], [
            '  NewState == \\/ Foo = Bar',
            '              '
        ]);
    });

    test('Indents definitions new line', () => {
        return assertOnTypeFormatting(doc, [
            '  NewState ==',
            '  {enter}'
        ], [
            '  NewState ==',
            '      '
        ]);
    });

    test('Indents operator definitions with AND', () => {
        return assertOnTypeFormatting(doc, [
            '  NewOp(a, b) == /\\ Foo = a',
            '  {enter}'
        ], [
            '  NewOp(a, b) == /\\ Foo = a',
            '                 '
        ]);
    });

    test('Indents operator definitions new line', () => {
        return assertOnTypeFormatting(doc, [
            '  NewOp(a, b) ==',
            '  {enter}'
        ], [
            '  NewOp(a, b) ==',
            '      '
        ]);
    });

    test('Doesn\'t indent definitions without AND / OR', () => {
        return assertOnTypeFormatting(doc, [
            '  NewState == TRUE',
            '  {enter}'
        ], [
            '  NewState == TRUE',
            '  '
        ]);
    });

    test('Doesn\'t indent definitions if it\'s not the first line', () => {
        return assertOnTypeFormatting(doc, [
            'Foo == \\/ <<>>',
            '',
            '{enter}'
        ], [
            'Foo == \\/ <<>>',
            '',
            ''
        ]);
    });

    test('Doesn\'t indent variables-block when it\'s not empty', () => {
        return assertOnTypeFormatting(doc, [
            '    variables foo = 10;',
            '    {enter}'
        ], [
            '    variables foo = 10;',
            '    '
        ]);
    });

    test('Doesn\'t indent simple block if it doesn\'t start on the previous line' , () => {
        return assertOnTypeFormatting(doc, [
            '    variables',
            '',
            '{enter}'
        ], [
            '    variables',
            '',
            ''
        ]);
    });

    test('Keeps simple block indentation', () => {
        return assertOnTypeFormatting(doc, [
            '    CONSTANTS',
            '        Foo,',
            '        {enter}'
        ], [
            '    CONSTANTS',
            '        Foo,',
            '        '
        ]);
    });

    test('Indents body first line and saves end of line', () => {
        return assertOnTypeFormatting(doc, [
                '    if TRUE then',
                '    {enter} \\* end of line'
            ], [
                '    if TRUE then',
                '         \\* end of line'
            ]
        );
    });

    test('Keeps indentation inside body', () => {
        return assertOnTypeFormatting(doc, [
                '    while a = 10 do',
                '        do_something(1);',
                '        {enter}(**)'
            ], [
                '    while a = 10 do',
                '        do_something(1);',
                '        (**)'
            ]
        );
    });

    test('Indents body lines after empty lines', () => {
        return assertOnTypeFormatting(doc, [
                '    define',
                '        FOO == 10',
                '',
                '{enter}(**)'
            ], [
                '    define',
                '        FOO == 10',
                '',
                '        (**)'
            ]
        );
    });

    test('Increases indentation of block ends', () => {
        return assertOnTypeFormatting(doc, [
                '    if TRUE then',
                '        skip;',
                ' en{d}'
            ], [
                '    if TRUE then',
                '        skip;',
                '    end'
            ]
        );
    });

    test('Doesnt indent block end when it is already intended', () => {
        return assertOnTypeFormatting(doc, [
                '    if TRUE then',
                '        skip;',
                '    end i{f}'
            ], [
                '    if TRUE then',
                '        skip;',
                '    end if'
            ]
        );
    });

    test('Ignores previous blocks', () => {
        return assertOnTypeFormatting(doc, [
                '    begin',
                '        while a < 20 do',
                '            a := a + 1;',
                '        end while;',
                '        {enter}'
            ], [
                '    begin',
                '        while a < 20 do',
                '            a := a + 1;',
                '        end while;',
                '        '
            ]
        );
    });

    test('Supports labelled blocks', () => {
        return assertOnTypeFormatting(doc, [
            '    Check: while a >= 10 do',
            '    {enter}'
        ], [
            '    Check: while a >= 10 do',
            '        '
        ]);
    });

    test('CAN IMPROVE: Indents to the body of enclosing block', () => {
        return assertOnTypeFormatting(doc, [
                '    begin',
                '        while a < 20 do',
                '            a := a + 1;',
                '        end while;',
                '',
                '{enter}(**)'
            ], [
                '    begin',
                '        while a < 20 do',
                '            a := a + 1;',
                '        end while;',
                '',
                '(**)'      // <-- ideally, we'd like this to be indented
            ]
        );
    });

    test('Respects formatting options, tabs', () => {
        return assertOnTypeFormatting(doc, [
            '    while TRUE do',
            '    {enter}'
        ], [
            '    while TRUE do',
            '    \t'
        ],
        { insertSpaces: false, tabSize: 4 });
    });

    test('Respects formatting options, 7 spaces', () => {
        return assertOnTypeFormatting(doc, [
            '    while TRUE do',
            '    {enter}'
        ], [
            '    while TRUE do',
            '           '
        ],
        { insertSpaces: true, tabSize: 7 });
    });

    test('Respects formatting options, 2 spaces', () => {
        return assertOnTypeFormatting(doc, [
            '    while TRUE do',
            '    {enter}'
        ], [
            '    while TRUE do',
            '      '
        ],
        { insertSpaces: true, tabSize: 2 });
    });
});

class DocInfo {
    constructor(
        readonly lines: string[],
        readonly position: vscode.Position,
        readonly char: string
    ) {}
}

async function assertOnTypeFormatting(
    doc: vscode.TextDocument,
    docLines: string[],
    expectLines: string[],
    options: vscode.FormattingOptions = OPT_4_SPACES
): Promise<undefined> {
    const docInfo = parseDocInfo(docLines);
    await replaceDocContents(doc, docInfo.lines.join('\n'));
    const tokenSrc = new vscode.CancellationTokenSource();
    const formatter = new TlaOnTypeFormattingEditProvider();
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

async function replaceDocContents(doc: vscode.TextDocument, content: string): Promise<boolean> {
    const edits = [];
    if (doc.lineCount > 0) {
        const lastLine = doc.lineAt(doc.lineCount - 1);
        const delEdit = vscode.TextEdit.delete(new vscode.Range(ZERO_POSITION, lastLine.range.end));
        edits.push(delEdit);
    }
    edits.push(vscode.TextEdit.insert(ZERO_POSITION, content));
    return applyDocEdits(doc.uri, edits);
}

async function applyDocEdits(docUri: vscode.Uri, edits: vscode.TextEdit[] | null | undefined): Promise<boolean> {
    if (!edits) {
        return false;
    }
    const wsEdit = new vscode.WorkspaceEdit();
    for (const edit of edits) {
        wsEdit.replace(docUri, edit.range, edit.newText);
    }
    return vscode.workspace.applyEdit(wsEdit);
}

function parseDocInfo(lines: string[]): DocInfo {
    let position;
    let char;
    let n = 0;
    const clearLines = lines.map(line => {
        let eLine = line;
        const matches = /^(.*){(\w+)}(.*)$/g.exec(line);
        if (matches) {
            char = matches[2] === 'enter' ? '\n' : matches[2];
            position = new vscode.Position(n, matches[1].length);
            eLine = matches[1] + (char === '\n' ? '' : char) + matches[3];
        }
        n += 1;
        return eLine;
    });
    if (!position || !char) {
        throw new Error('Caret position not found.');
    }
    return new DocInfo(clearLines, position, char);
}
