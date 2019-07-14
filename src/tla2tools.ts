import * as vscode from 'vscode';
import fs = require('fs');
import path = require('path');
import cp = require('child_process');

const javaCmd = 'java' + (process.platform === 'win32' ? '.exe' : '');

class ToolResult {
    readonly err: any;
    readonly stdout: String;
    readonly stderr: String;

    constructor (err: any, stdout: String, stderr: String) {
        this.err = err;
        this.stdout = stdout;
        this.stderr = stderr;
    }
}

class DMessage {
    readonly filePath: string;
    readonly diagnostic: vscode.Diagnostic;

    constructor(filePath: string, range: vscode.Range, message: string) {
        this.filePath = filePath;
        this.diagnostic = new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Error);
    }
}

/**
 * Checks .tla file:
 * - Transpiles PlusCal to TLA+
 * - Check resulting TLA+ speck
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
    editor.document.save().then(() => doCheckFile(editor.document.uri, diagnostic));
}

async function doCheckFile(fileUri: vscode.Uri, diagnostic: vscode.DiagnosticCollection) {
    const javaPath = buildJavaPath();
    if (!javaPath) {
        return;
    }
    const toolsJarPath = path.resolve(__dirname, '../tools/tla2tools.jar');
    const toolsArgs = ['-cp', toolsJarPath];

    diagnostic.clear();
    transpilePlusCal(javaPath, toolsArgs, fileUri)
    .then(pcalMessages => {
        parseSpec(javaPath, toolsArgs, fileUri)
        .then(specMessages => {
            const messages = pcalMessages.concat(specMessages);
            const uri2diag = new Map<string, vscode.Diagnostic[]>();
            messages.forEach(d => {
                let list = uri2diag.get(d.filePath);
                if (!list) {
                    list = [];
                    uri2diag.set(d.filePath, list);
                }
                list.push(d.diagnostic);
            });
            uri2diag.forEach((diags, path) => diagnostic.set(vscode.Uri.parse('file://' + path), diags));
        });
    });
}

/**
 * Transpiles PlusCal code in the current .tla file to TLA+ code in the same file.
 */
function transpilePlusCal(javaPath: string, toolsArgs: string[], fileUri: vscode.Uri): Promise<DMessage[]> {
    let workDir = path.dirname(fileUri.fsPath);
    return runTool(javaPath, toolsArgs.concat(["pcal.trans", fileUri.fsPath]), workDir)
            .then(res => parsePlusCalOutput(res, fileUri.fsPath));
}

/**
 * Parses the resulting TLA+ spec.
 */
function parseSpec(javaPath: string, toolsArgs: string[], fileUri: vscode.Uri): Promise<DMessage[]> {
    let workDir = path.dirname(fileUri.fsPath);
    return runTool(javaPath, toolsArgs.concat(["tla2sany.SANY", fileUri.fsPath]), workDir)
            .then(res => parseSanyOutput(res));
}

function runTool(javaPath: string, args: string[], workDir: string): Promise<ToolResult> {
    let p: cp.ChildProcess;
    return new Promise((resolve, reject) => {
        p = cp.execFile(javaPath, args, { env: [], cwd: workDir }, (err, stdout, stderr) => {
            resolve(new ToolResult(err, stdout, stderr));
        });
    });
}

function parsePlusCalOutput(res: ToolResult, filePath: string): DMessage[] {
    if (!res.err) {
        return [];
    }
    if ((<any>res.err).code !== 255) {
        reportBrokenToolchain(res.err);
        return [];
    }

    let lines = res.stdout.split('\n');
    let messages: DMessage[] = [];
    for (let l = 0; l < lines.length; l++) {
        if (lines[l] === '') {
            continue;
        }
        l += tryParsePlusCalMessage(lines, l, filePath, messages);
    }
    if (messages.length === 0) {
        vscode.window.showErrorMessage('Cannot parse PlusCal output');
        console.log("----- PlusCal transpiler STDOUT -----\n" + res.stdout + '-------------------');
    }
    return messages;
}

function tryParsePlusCalMessage(lines: string[], idx: number, filePath: string, messages: DMessage[]): number {
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
    // Position
    const rxPosition = /^\s+(?:at )?line (\d+), column (\d+).?\s*$/g;
    const posMatches = rxPosition.exec(lines[idx + 2]);
    if (!posMatches || posMatches.length !== 3) {
        return 0;
    }
    const line = parseInt(posMatches[1]) - 1;
    const col = parseInt(posMatches[2]);
    messages.push(new DMessage(
        filePath,
        new vscode.Range(line, col, line, col),
        textMatches[1]
    ));
    return 2;
}

function parseSanyOutput(res: ToolResult): DMessage[] {
    console.log('SANY ERR: ' + res.err);
    console.log('---- SANY STDOUT ----\n' + res.stdout);
    console.log('---- SANY STDERR ----\n' + res.stderr);
    if (res.err && (<any>res.err).code !== 255) {
        reportBrokenToolchain(res.err);
        return [];
    }

    const lines = res.stdout.split('\n');
    const messages: DMessage[] = [];
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
        } else if (errors) {
            l += tryParseSanyError(lines, l, modPaths, messages);
        } else if (fatalErrors) {
            l += tryParseSanyFatalError(lines, l, curModPath, messages);
        }
    }
    return messages;
}

function tryParseSanyError(lines: string[], idx: number, modPaths: Map<string, string>, messages: DMessage[]): number {
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
    messages.push(new DMessage(
        modPath,
        new vscode.Range(parseInt(posMatches[1]) - 1, parseInt(posMatches[2]) - 1, parseInt(posMatches[3]) - 1, parseInt(posMatches[4])),
        lines[idx + 2]
    ));
    return 2;
}

function tryParseSanyFatalError(lines: string[], idx: number, modPath: string, messages: DMessage[]): number {
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
    messages.push(new DMessage(
        modPath,
        new vscode.Range(line, col, line, col),
        lines[idx]
    ));
    return 1;
}

function reportBrokenToolchain(err: any) {
    // Toolchain is either not installed or broken
    console.log('Toolchain problem: ' + err.message);
    vscode.window.showErrorMessage('Toolchain is broken');
}

function buildJavaPath() {
    const javaHome = vscode.workspace.getConfiguration().get<string>('tlaplus.java.home');
    let javaPath = javaCmd;
    if (javaHome) {
        const homeUri = vscode.Uri.parse(javaHome);
        const javaPath = homeUri.fsPath + path.sep + 'bin' + path.sep + javaCmd;
        if (!fs.existsSync(javaPath)) {
            vscode.window.showErrorMessage('Java command not found. Check the Java Home configuration property.');
            return null;
        }
    }
    return javaPath;
}