import * as vscode from 'vscode';
import path = require('path');
import * as tools from './tla2tools';
import {DCollection} from './diagnostic';

/**
 * Parses .tla module:
 * - Transpiles PlusCal to TLA+
 * - Parses resulting TLA+ specification and checks for syntax errors
 */
export function parseModule(diagnostic: vscode.DiagnosticCollection) {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot find a TLA+ file to transpile');
        return;
    }
    if (editor.document.languageId !== 'tlaplus') {
        vscode.window.showWarningMessage('File in the active editor is not a TLA+ file, it cannot be transpiled');
        return;
    }
    editor.document.save().then(() => doParseFile(editor.document.uri, diagnostic));
}

async function doParseFile(fileUri: vscode.Uri, diagnostic: vscode.DiagnosticCollection) {
    const javaPath = tools.buildJavaPath();
    if (!javaPath) {
        return;
    }
    const toolsArgs = ['-cp', tools.toolsJarPath];

    let messages = await transpilePlusCal(javaPath, toolsArgs, fileUri);
    let specMessages = await parseSpec(javaPath, toolsArgs, fileUri);
    messages.addAll(specMessages);
    messages.apply(diagnostic);
}

/**
 * Transpiles PlusCal code in the current .tla file to TLA+ code in the same file.
 */
async function transpilePlusCal(javaPath: string, toolsArgs: string[], fileUri: vscode.Uri): Promise<DCollection> {
    let workDir = path.dirname(fileUri.fsPath);
    const res = await tools.executeJavaProcess(javaPath, toolsArgs.concat(["pcal.trans", fileUri.fsPath]), workDir);
    return parsePlusCalOutput(res, fileUri.fsPath);
}

/**
 * Parses the resulting TLA+ spec.
 */
async function parseSpec(javaPath: string, toolsArgs: string[], fileUri: vscode.Uri): Promise<DCollection> {
    let workDir = path.dirname(fileUri.fsPath);
    const res = await tools.executeJavaProcess(javaPath, toolsArgs.concat(["tla2sany.SANY", fileUri.fsPath]), workDir);
    return parseSanyOutput(res);
}

function parsePlusCalOutput(res: tools.ToolResult, filePath: string): DCollection {
    let dCol = new DCollection();
    if (!res.err) {
        return dCol;
    }
    if ((<any>res.err).code !== 255) {
        tools.reportBrokenToolchain(res.err);
        return dCol;
    }

    let lines = res.stdout.split('\n');
    for (let l = 0; l < lines.length; l++) {
        if (lines[l] === '') {
            continue;
        }
        l += tryParsePlusCalMessage(lines, l, filePath, dCol);
    }
    return dCol;
}

function tryParsePlusCalMessage(lines: string[], idx: number, filePath: string, dCol: DCollection): number {
    if (lines.length < idx + 3) {
        return 0;
    }
    // Header
    if (!lines[idx].endsWith(':')) {
        return 0;
    }
    // Message text
    const rxText = /^\s+--\s*(.*)$/g;
    const textMatches = rxText.exec(lines[idx + 1]);
    if (!textMatches || textMatches.length !== 2) {
        return 0;
    }
    const message = textMatches[1];
    if (message.startsWith('Beginning of algorithm string --algorithm not found')) {
        // This message means that there were no PlusCal code in the file, we can ignore that
        return 1;
    }
    // Position
    let line = 0;
    let col = 0;
    if (lines[idx + 2].length > 0) {
        const rxPosition = /^\s+(?:at )?line (\d+), column (\d+).?\s*$/g;
        const posMatches = rxPosition.exec(lines[idx + 2]);
        if (!posMatches || posMatches.length !== 3) {
            return 0;
        }
        line = parseInt(posMatches[1]) - 1;
        col = parseInt(posMatches[2]);
    }
    dCol.addMessage(filePath, new vscode.Range(line, col, line, col), message);
    return 2;
}

function parseSanyOutput(res: tools.ToolResult): DCollection {
    const dCol = new DCollection();
    if (res.err && (<any>res.err).code !== 255) {
        tools.reportBrokenToolchain(res.err);
        return dCol;
    }

    const lines = res.stdout.split('\n');
    const modPaths: Map<string, string> = new Map();
    let errors = false;
    let fatalErrors = false;
    let curModPath = '';
    for (let l = 0; l < lines.length; l++) {
        const line = lines[l];
        if (line === '') {
            continue;
        }
        if (line.startsWith('*** Errors:')) {
            errors = true;
            fatalErrors = false;
        } else if (line.startsWith('***Parse Error***')) {
            errors = false;
            fatalErrors = true;
        } else if (!errors && line.startsWith('Parsing file ')) {
            curModPath = line.substring(13);
            const sid = curModPath.lastIndexOf(path.sep);
            const modName = curModPath.substring(sid + 1, curModPath.length - 4);   // remove path and .tla
            modPaths.set(modName, curModPath);
            dCol.addFilePath(curModPath);
        } else if (errors) {
            l += tryParseSanyError(lines, l, modPaths, dCol);
        } else if (fatalErrors) {
            l += tryParseSanyFatalError(lines, l, curModPath, dCol);
        }
    }
    return dCol;
}

function tryParseSanyError(lines: string[], idx: number, modPaths: Map<string, string>, dCol: DCollection): number {
    if (lines.length < idx + 3) {
        return 0;
    }
    // Position
    const rxPosition = /^\s*line (\d+), col (\d+) to line (\d+), col (\d+) of module ([a-zA-Z0-9_]+)\s*$/g;
    const posMatches = rxPosition.exec(lines[idx]);
    if (!posMatches || posMatches.length !== 6) {
        return 0;
    }
    let modPath = modPaths.get(posMatches[5]) || '';
    // Empty line
    if (lines[idx + 1] !== '') {
        return 0;
    }
    dCol.addMessage(
        modPath,
        new vscode.Range(parseInt(posMatches[1]) - 1, parseInt(posMatches[2]) - 1, parseInt(posMatches[3]) - 1, parseInt(posMatches[4])),
        lines[idx + 2]
    );
    return 2;
}

function tryParseSanyFatalError(lines: string[], idx: number, modPath: string, dCol: DCollection): number {
    if (lines.length < idx + 2) {
        return 0;
    }
    // Position
    const rxPosition = /^.*\s+at line (\d+), column (\d+)\s+.*$/g;
    const posMatches = rxPosition.exec(lines[idx + 1]);
    if (!posMatches || posMatches.length !== 3) {
        return 0;
    }
    const line = parseInt(posMatches[1]) - 1;
    const col = parseInt(posMatches[2]) - 1;
    dCol.addMessage(modPath, new vscode.Range(line, col, line, col), lines[idx]);
    return 1;
}
