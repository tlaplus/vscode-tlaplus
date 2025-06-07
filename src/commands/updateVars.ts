import * as vscode from 'vscode';

interface VarsInfo {
    startLine: number;
    endLine: number;
    startChar: number;
    endChar: number;
    currentVars: string[];
    hasNestedTuples: boolean;
}

/**
 * Extracts all variables from VARIABLE(S) declarations
 * Parses the document text directly for reliability in tests
 */
async function extractAllVariables(document: vscode.TextDocument): Promise<string[]> {
    const text = document.getText();
    const lines = text.split('\n');
    const variables: string[] = [];

    // State for multi-line variable declarations
    let inVariableDecl = false;
    let currentVarList = '';

    for (const line of lines) {
        // Check for VARIABLE or VARIABLES keyword
        const varMatch = line.match(/^\s*(VARIABLE|VARIABLES)\s+(.*)$/);
        if (varMatch) {
            // If we were already in a variable declaration, process the previous one
            if (currentVarList) {
                // Remove comments
                const cleanList = currentVarList.replace(/\\\*.*/g, '').replace(/\(\*[^*]*\*\)/g, '');

                // Split by comma and extract variable names
                const varNames = cleanList.split(',');
                for (const varName of varNames) {
                    const trimmed = varName.trim();
                    if (trimmed && /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(trimmed)) {
                        variables.push(trimmed);
                    }
                }
            }

            inVariableDecl = true;
            currentVarList = varMatch[2];
        } else if (inVariableDecl) {
            // Check if line continues variable list (starts with whitespace and contains identifiers)
            const continueMatch = line.match(/^\s+([a-zA-Z_][a-zA-Z0-9_]*.*)/);
            if (continueMatch) {
                currentVarList += ' ' + continueMatch[1];
            } else {
                // End of variable declaration - process it
                if (currentVarList) {
                    // Remove comments
                    const cleanList = currentVarList.replace(/\\\*.*/g, '').replace(/\(\*[^*]*\*\)/g, '');

                    // Split by comma and extract variable names
                    const varNames = cleanList.split(',');
                    for (const varName of varNames) {
                        const trimmed = varName.trim();
                        if (trimmed && /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(trimmed)) {
                            variables.push(trimmed);
                        }
                    }
                    currentVarList = '';
                }
                inVariableDecl = false;
            }
        }
    }

    // Handle case where file ends with variable declaration
    if (currentVarList) {
        currentVarList = currentVarList.replace(/\\\*.*/g, '').replace(/\(\*[^*]*\*\)/g, '');
        const varNames = currentVarList.split(',');
        for (const varName of varNames) {
            const trimmed = varName.trim();
            if (trimmed && /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(trimmed)) {
                variables.push(trimmed);
            }
        }
    }

    return variables;
}

/**
 * Finds the vars definition in the document
 * Handles multi-line tuples with state machine approach
 */
function findVarsDefinition(document: vscode.TextDocument): VarsInfo | undefined {
    const text = document.getText();
    const lines = text.split('\n');

    // State machine states
    enum State {
        SEARCHING,
        COLLECTING,
        COMPLETE
    }

    let state = State.SEARCHING;
    let startLine = -1;
    let endLine = -1;
    let startChar = -1;
    let endChar = -1;
    let nestingLevel = 0;

    for (let lineNum = 0; lineNum < lines.length; lineNum++) {
        const line = lines[lineNum];

        if (state === State.SEARCHING) {
            const varsMatch = line.match(/^(\s*)vars\s*==\s*<</);
            if (varsMatch) {
                state = State.COLLECTING;
                startLine = lineNum;
                startChar = varsMatch[0].indexOf('<<');
                nestingLevel = 1;

                // Check if it's all on one line
                const startIdx = varsMatch[0].length;
                for (let i = startIdx; i < line.length; i++) {
                    if (line[i] === '<' && i + 1 < line.length && line[i + 1] === '<') {
                        nestingLevel++;
                        i++; // Skip next character
                    } else if (line[i] === '>' && i + 1 < line.length && line[i + 1] === '>') {
                        nestingLevel--;
                        i++; // Skip next character

                        if (nestingLevel === 0) {
                            state = State.COMPLETE;
                            endLine = lineNum;
                            endChar = i + 1;
                            break;
                        }
                    }
                }
            }
        } else if (state === State.COLLECTING) {
            // Count nesting levels
            for (let i = 0; i < line.length; i++) {
                if (line[i] === '<' && i + 1 < line.length && line[i + 1] === '<') {
                    nestingLevel++;
                    i++; // Skip next character
                } else if (line[i] === '>' && i + 1 < line.length && line[i + 1] === '>') {
                    nestingLevel--;
                    i++; // Skip next character

                    if (nestingLevel === 0) {
                        state = State.COMPLETE;
                        endLine = lineNum;
                        endChar = i + 1;
                        break;
                    }
                }
            }
        }

        if (state === State.COMPLETE) {
            break;
        }
    }

    if (state !== State.COMPLETE) {
        return undefined;
    }

    // Extract full content for variable extraction
    let fullVarsContent = '';
    if (startLine === endLine) {
        // Single line: extract content between << and >>
        fullVarsContent = lines[startLine].substring(startChar + 2, lines[endLine].lastIndexOf('>>'));
    } else {
        // Multi-line: combine all lines
        fullVarsContent = lines[startLine].substring(startChar + 2);
        for (let i = startLine + 1; i < endLine; i++) {
            fullVarsContent += '\n' + lines[i];
        }
        fullVarsContent += '\n' + lines[endLine].substring(0, lines[endLine].lastIndexOf('>>'));
    }

    // Extract variables from the vars content
    const currentVars = extractVariablesFromTuple(fullVarsContent);
    const hasNestedTuples = fullVarsContent.includes('<<');

    return {
        startLine,
        endLine,
        startChar,
        endChar,
        currentVars,
        hasNestedTuples
    };
}

/**
 * Extracts variable names from a tuple string
 */
function extractVariablesFromTuple(tupleContent: string): string[] {
    // Remove comments
    const noComments = tupleContent.replace(/\\\\\\*.*/g, '').replace(/\(\\*[^*]*\\*\)/g, '');

    // Simple extraction for basic cases - will be enhanced in Phase 2
    const variables: string[] = [];
    const matches = noComments.match(/[a-zA-Z_][a-zA-Z0-9_]*/g);

    if (matches) {
        for (const match of matches) {
            // Filter out TLA+ keywords that might appear
            if (!['vars', 'TRUE', 'FALSE'].includes(match)) {
                variables.push(match);
            }
        }
    }

    return variables;
}

/**
 * Creates text edit to update vars tuple
 * Preserves formatting, indentation, and comments
 */
function createVarsUpdateEdit(
    document: vscode.TextDocument,
    varsInfo: VarsInfo,
    newVars: string[]
): vscode.TextEdit {
    const startPos = new vscode.Position(varsInfo.startLine, varsInfo.startChar);
    const endPos = new vscode.Position(varsInfo.endLine, varsInfo.endChar);

    // Check if original was multi-line
    const isMultiLine = varsInfo.startLine !== varsInfo.endLine;

    if (isMultiLine) {
        // Preserve multi-line formatting
        const lines = document.getText().split('\n');
        const firstLine = lines[varsInfo.startLine];
        const indentMatch = firstLine.match(/^(\s*)/);
        const baseIndent = indentMatch ? indentMatch[1] : '';

        // Determine items per line by analyzing the original format
        const originalContent = extractOriginalVarsContent(document, varsInfo);
        const itemsPerLine = detectItemsPerLine(originalContent);

        // Build formatted multi-line tuple
        let result = '<<\n';
        const innerIndent = baseIndent + '    ';

        for (let i = 0; i < newVars.length; i++) {
            if (i % itemsPerLine === 0 && i > 0) {
                result = result.trimEnd() + '\n';
            }

            if (i % itemsPerLine === 0) {
                result += innerIndent;
            }

            result += newVars[i];

            if (i < newVars.length - 1) {
                result += ', ';
            }
        }

        result += '\n' + baseIndent + '>>';

        return vscode.TextEdit.replace(new vscode.Range(startPos, endPos), result);
    } else {
        // Single-line formatting
        const newVarsTuple = `<<${newVars.join(', ')}>>`;

        // Check if it's getting too long (> 80 chars) or has many variables
        const linePrefix = document.lineAt(varsInfo.startLine).text.substring(0, varsInfo.startChar);
        if ((linePrefix.length + newVarsTuple.length > 80 || newVars.length > 10) && newVars.length > 3) {
            // Convert to multi-line
            const indentMatch = linePrefix.match(/^(\s*)/);
            const baseIndent = indentMatch ? indentMatch[1] : '';

            let result = '<<\n';
            const innerIndent = baseIndent + '    ';

            // Default to 4 items per line for long lists
            const itemsPerLine = 4;

            for (let i = 0; i < newVars.length; i++) {
                if (i % itemsPerLine === 0) {
                    if (i > 0) {result = result.trimEnd() + '\n';}
                    result += innerIndent;
                }

                result += newVars[i];

                if (i < newVars.length - 1) {
                    result += ', ';
                }
            }

            result += '\n' + baseIndent + '>>';

            return vscode.TextEdit.replace(new vscode.Range(startPos, endPos), result);
        }

        return vscode.TextEdit.replace(new vscode.Range(startPos, endPos), newVarsTuple);
    }
}

/**
 * Extracts the original vars content for analysis
 */
function extractOriginalVarsContent(document: vscode.TextDocument, varsInfo: VarsInfo): string {
    const lines = document.getText().split('\n');

    if (varsInfo.startLine === varsInfo.endLine) {
        return lines[varsInfo.startLine].substring(varsInfo.startChar, varsInfo.endChar);
    }

    let content = lines[varsInfo.startLine].substring(varsInfo.startChar);
    for (let i = varsInfo.startLine + 1; i < varsInfo.endLine; i++) {
        content += '\n' + lines[i];
    }
    content += '\n' + lines[varsInfo.endLine].substring(0, varsInfo.endChar);

    return content;
}

/**
 * Detects how many variables per line in the original format
 */
function detectItemsPerLine(varsContent: string): number {
    // Remove << and >> and trim
    const innerContent = varsContent
        .replace(/^<<\s*/s, '')
        .replace(/\s*>>$/s, '')
        .trim();

    const lines = innerContent.split('\n').filter(line => line.trim());

    if (lines.length === 0) {return 4;} // Default
    if (lines.length === 1) {
        // For single line, count the variables
        const varMatches = lines[0].match(/[a-zA-Z_][a-zA-Z0-9_]*/g);
        return varMatches ? varMatches.length : 4;
    }

    // For multi-line, find the most common pattern
    // Look at the first line that has the most complete set
    for (const line of lines) {
        const trimmedLine = line.trim();
        // Skip lines that end with just one variable (likely incomplete)
        if (!trimmedLine.endsWith(',')) {
            continue;
        }

        const varMatches = trimmedLine.match(/[a-zA-Z_][a-zA-Z0-9_]*/g);
        if (varMatches && varMatches.length > 0) {
            return varMatches.length;
        }
    }

    // If no complete lines found, use the max
    let maxItems = 0;
    for (const line of lines) {
        const varMatches = line.match(/[a-zA-Z_][a-zA-Z0-9_]*/g);
        if (varMatches && varMatches.length > maxItems) {
            maxItems = varMatches.length;
        }
    }

    return maxItems > 0 ? maxItems : 4;
}

/**
 * Detects if document contains PlusCal algorithm
 */
function hasPlusCalAlgorithm(document: vscode.TextDocument): boolean {
    const text = document.getText();
    // PlusCal algorithms start with (*--algorithm or (*--fair algorithm
    return /\(\*--(?:fair )?algorithm/m.test(text);
}

/**
 * Main command implementation
 */
export async function updateVarsCommand(): Promise<void> {
    // 1. Get active document
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showInformationMessage('No active TLA+ file');
        return;
    }

    const document = editor.document;
    if (document.languageId !== 'tlaplus') {
        vscode.window.showInformationMessage('This command only works with TLA+ files');
        return;
    }

    // 2. Extract all variables
    const allVariables = await extractAllVariables(document);
    if (allVariables.length === 0) {
        vscode.window.showInformationMessage('No variables found in the document');
        return;
    }

    // 3. Find vars definition
    const varsInfo = findVarsDefinition(document);
    if (!varsInfo) {
        vscode.window.showInformationMessage("No 'vars' definition found in the current file");
        return;
    }

    // 4. Check for PlusCal and handle pc/stack variables
    const hasPlusCal = hasPlusCalAlgorithm(document);
    let filteredVariables = [...allVariables];

    if (hasPlusCal) {
        // Check configuration for including PlusCal variables
        const config = vscode.workspace.getConfiguration('tlaplus.refactor');
        const includePlusCalVars = config.get<boolean>('includePlusCalVariables', true);

        if (!includePlusCalVars) {
            // Filter out pc and stack variables
            filteredVariables = allVariables.filter(v => v !== 'pc' && v !== 'stack');

            // Show info message about filtered variables
            const excluded = allVariables.filter(v => v === 'pc' || v === 'stack');
            if (excluded.length > 0) {
                vscode.window.showInformationMessage(
                    `PlusCal variables excluded: ${excluded.join(', ')}. Change setting to include them.`
                );
            }
        }
    }

    // 5. Compare and update if needed
    const currentVarsSet = new Set(varsInfo.currentVars);
    const filteredVarsSet = new Set(filteredVariables);

    // Check if update is needed
    if (currentVarsSet.size === filteredVarsSet.size &&
        [...currentVarsSet].every(v => filteredVarsSet.has(v))) {
        vscode.window.showInformationMessage('vars already up to date');
        return;
    }

    // 6. Apply edit with preview
    const edit = createVarsUpdateEdit(document, varsInfo, filteredVariables);
    const workspaceEdit = new vscode.WorkspaceEdit();
    workspaceEdit.set(document.uri, [edit]);

    await vscode.workspace.applyEdit(workspaceEdit);
    vscode.window.showInformationMessage(`Updated vars with ${filteredVariables.length} variables`);
}