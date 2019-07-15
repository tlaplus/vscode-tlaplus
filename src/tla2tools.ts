import * as vscode from 'vscode';
import fs = require('fs');
import path = require('path');
import cp = require('child_process');

export const toolsJarPath = path.resolve(__dirname, '../tools/tla2tools.jar');
const javaCmd = 'java' + (process.platform === 'win32' ? '.exe' : '');

/**
 * Result of a command execution.
 */
export class ToolResult {
    readonly err: any;
    readonly stdout: String;
    readonly stderr: String;

    constructor (err: any, stdout: String, stderr: String) {
        this.err = err;
        this.stdout = stdout;
        this.stderr = stderr;
    }
}

/**
 * Executes a Java process.
 */
export function executeJavaProcess(javaPath: string, args: string[], workDir: string): Promise<ToolResult> {
    let p: cp.ChildProcess;
    return new Promise((resolve, reject) => {
        p = cp.execFile(javaPath, args, { env: [], cwd: workDir }, (err, stdout, stderr) => {
            resolve(new ToolResult(err, stdout, stderr));
        });
    });
}

export function buildJavaPath() {
    const javaHome = vscode.workspace.getConfiguration().get<string>('tlaplus.java.home');
    let javaPath = javaCmd;
    if (javaHome) {
        const homeUri = vscode.Uri.parse('file://' + javaHome);
        const javaPath = homeUri.fsPath + path.sep + 'bin' + path.sep + javaCmd;
        if (!fs.existsSync(javaPath)) {
            vscode.window.showErrorMessage('Java command not found. Check the Java Home configuration property.');
            return null;
        }
    }
    return javaPath;
}

export function reportBrokenToolchain(err: any) {
    console.log('Toolchain problem: ' + err.message);
    vscode.window.showErrorMessage('Toolchain is broken');
}
