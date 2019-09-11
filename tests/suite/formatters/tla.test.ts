import * as vscode from 'vscode';
import { assertOnTypeFormatting, OPT_4_SPACES } from './formatting';
import { TlaOnTypeFormattingEditProvider } from '../../../src/formatters/tla';
import { LANG_TLAPLUS } from '../../../src/common';

suite('TLA On Type Formatting Test Suite', () => {
    let doc: vscode.TextDocument;

    suiteSetup(async () => {
        doc = await vscode.workspace.openTextDocument({ language: LANG_TLAPLUS });
    });

    suiteTeardown(async () => {
        await vscode.window.showTextDocument(doc, {preview: true, preserveFocus: false});
        return vscode.commands.executeCommand('workbench.action.closeActiveEditor');
    });

    test('Indents begin-block body', () => {
        return assertTlaOnTypeFormatting(doc, [
                'begin',
                '{enter}(**)'
            ], [
                'begin',
                '    (**)'
            ]
        );
    });

    test('Indents define-block body', () => {
        return assertTlaOnTypeFormatting(doc, [
                'define',
                '{enter}(**)'
            ], [
                'define',
                '    (**)'
            ]
        );
    });

    test('Indents define-block closing', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
                'macro foo(x) begin',
                '{enter}(**)'
            ], [
                'macro foo(x) begin',
                '    (**)'
            ]
        );
    });

    test('Indents macro-block closing', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
                'procedure foo(x) begin',
                '{enter}(**)'
            ], [
                'procedure foo(x) begin',
                '    (**)'
            ]
        );
    });

    test('Indents procedure-block closing', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
                '    if TRUE then',
                '    {enter}(**)'
            ], [
                '    if TRUE then',
                '        (**)'
            ]
        );
    });

    test('Indents else-line', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
                '    either',
                '    {enter}(**)'
            ], [
                '    either',
                '        (**)'
            ]
        );
    });

    test('Indents or-line', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
                '    while a < b do',
                '    {enter}(**)'
            ], [
                '    while a < b do',
                '        (**)'
            ]
        );
    });

    test('Indents while-block closing', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
                'with a = 100 do',
                '{enter}(**)'
            ], [
                'with a = 100 do',
                '    (**)'
            ]
        );
    });

    test('Indents with-block closing', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
            '    variables',
            '    {enter}'
        ], [
            '    variables',
            '        '
        ]);
    });

    test('Indents VARIABLES-block when it\'s empty', () => {
        return assertTlaOnTypeFormatting(doc, [
            '    VARIABLES',
            '    {enter}'
        ], [
            '    VARIABLES',
            '        '
        ]);
    });

    test('Indents VARIABLE-block when it\'s empty', () => {
        return assertTlaOnTypeFormatting(doc, [
            '    VARIABLE',
            '    {enter}'
        ], [
            '    VARIABLE',
            '        '
        ]);
    });

    test('Indents CONSTANTS-block when it\'s empty', () => {
        return assertTlaOnTypeFormatting(doc, [
            '    CONSTANTS',
            '    {enter}'
        ], [
            '    CONSTANTS',
            '        '
        ]);
    });

    test('Indents CONSTANT-block when it\'s empty', () => {
        return assertTlaOnTypeFormatting(doc, [
            '    CONSTANT',
            '    {enter}'
        ], [
            '    CONSTANT',
            '        '
        ]);
    });

    test('Indents label-blocks', () => {
        return assertTlaOnTypeFormatting(doc, [
            '    LabelA:',
            '    {enter}'
        ], [
            '    LabelA:',
            '        '
        ]);
    });

    test('Indents definitions with AND', () => {
        return assertTlaOnTypeFormatting(doc, [
            '  NewState == /\\ TRUE',
            '  {enter}'
        ], [
            '  NewState == /\\ TRUE',
            '              '
        ]);
    });

    test('Indents definitions with OR', () => {
        return assertTlaOnTypeFormatting(doc, [
            '  NewState == \\/ Foo = Bar',
            '  {enter}'
        ], [
            '  NewState == \\/ Foo = Bar',
            '              '
        ]);
    });

    test('Indents definitions new line', () => {
        return assertTlaOnTypeFormatting(doc, [
            '  NewState ==',
            '  {enter}'
        ], [
            '  NewState ==',
            '      '
        ]);
    });

    test('Indents operator definitions with AND', () => {
        return assertTlaOnTypeFormatting(doc, [
            '  NewOp(a, b) == /\\ Foo = a',
            '  {enter}'
        ], [
            '  NewOp(a, b) == /\\ Foo = a',
            '                 '
        ]);
    });

    test('Indents operator definitions new line', () => {
        return assertTlaOnTypeFormatting(doc, [
            '  NewOp(a, b) ==',
            '  {enter}'
        ], [
            '  NewOp(a, b) ==',
            '      '
        ]);
    });

    test('Doesn\'t indent definitions without AND / OR', () => {
        return assertTlaOnTypeFormatting(doc, [
            '  NewState == TRUE',
            '  {enter}'
        ], [
            '  NewState == TRUE',
            '  '
        ]);
    });

    test('Doesn\'t indent definitions if it\'s not the first line', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
            '    variables foo = 10;',
            '    {enter}'
        ], [
            '    variables foo = 10;',
            '    '
        ]);
    });

    test('Doesn\'t indent simple block if it doesn\'t start on the previous line' , () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
                '    if TRUE then',
                '    {enter} \\* end of line'
            ], [
                '    if TRUE then',
                '         \\* end of line'
            ]
        );
    });

    test('Keeps indentation inside body', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
            '    Check: while a >= 10 do',
            '    {enter}'
        ], [
            '    Check: while a >= 10 do',
            '        '
        ]);
    });

    test('CAN IMPROVE: Indents to the body of enclosing block', () => {
        return assertTlaOnTypeFormatting(doc, [
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
        return assertTlaOnTypeFormatting(doc, [
            '    while TRUE do',
            '    {enter}'
        ], [
            '    while TRUE do',
            '    \t'
        ],
        { insertSpaces: false, tabSize: 4 });
    });

    test('Respects formatting options, 7 spaces', () => {
        return assertTlaOnTypeFormatting(doc, [
            '    while TRUE do',
            '    {enter}'
        ], [
            '    while TRUE do',
            '           '
        ],
        { insertSpaces: true, tabSize: 7 });
    });

    test('Respects formatting options, 2 spaces', () => {
        return assertTlaOnTypeFormatting(doc, [
            '    while TRUE do',
            '    {enter}'
        ], [
            '    while TRUE do',
            '      '
        ],
        { insertSpaces: true, tabSize: 2 });
    });
});

function assertTlaOnTypeFormatting(
    doc: vscode.TextDocument,
    docLines: string[],
    expectLines: string[],
    options: vscode.FormattingOptions = OPT_4_SPACES
): Promise<void> {
    return assertOnTypeFormatting(
        new TlaOnTypeFormattingEditProvider(),
        doc,
        docLines,
        expectLines,
        options
    );
}
