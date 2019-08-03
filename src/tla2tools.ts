import * as vscode from 'vscode';
import * as path from 'path';
import * as cp from 'child_process';
import * as fs from 'fs';
import { ChildProcess, SpawnOptions, spawn, exec } from 'child_process';
import { pathToUri } from './common';
import { JavaVersionParser } from './parsers/javaVersion';

const javaCmd = 'java' + (process.platform === 'win32' ? '.exe' : '');
const javaBaseArgs = ['-XX:+UseParallelGC'];
const toolsJarPath = path.resolve(__dirname, '../tools/tla2tools.jar');

/**
 * Thrown when there's some problem with Java or TLA+ tooling.
 */
export class ToolingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

/**
 * Executes a TLA+ tool.
 */
export function runTool(toolName: string, filePath: string, toolArgs?: string[]): cp.ChildProcess {
    const eArgs = ['-cp', toolsJarPath, toolName].concat(toolArgs || []);
    eArgs.push(filePath);
    const process = executeJavaProcess(eArgs, { cwd: path.dirname(filePath) });
    process.on('close', (code) => {
        console.log('Java exit code ' + code);
    });
    return process;
}

/**
 * Kills the given process.
 */
export function stopProcess(p: cp.ChildProcess) {
    if (!p.killed) {
        p.kill('SIGINT');
    }
}

function checkJavaVersion() {
    const proc = executeJavaProcess(['-version']);
    const parser = new JavaVersionParser(proc.stderr);
    parser.readAll()
        .then(ver => console.log('Java version ' + ver));
}

export function reportBrokenToolchain(err: any) {
    console.log('Toolchain problem: ' + err.message);
    vscode.window.showErrorMessage('Toolchain is broken');
}

function executeJavaProcess(args: string[], options?: SpawnOptions): ChildProcess {
    const javaPath = buildJavaPath();
    const eArgs = javaBaseArgs.concat(args);
    return spawn(javaPath, eArgs, options);
}

function buildJavaPath(): string {
    const javaHome = vscode.workspace.getConfiguration().get<string>('tlaplus.java.home');
    const javaPath = javaCmd;
    if (javaHome) {
        const homeUri = pathToUri(javaHome);
        const javaPath = homeUri.fsPath + path.sep + 'bin' + path.sep + javaCmd;
        if (!fs.existsSync(javaPath)) {
            throw new ToolingError('Java command not found. Check the Java Home configuration property.');
        }
    }
    return javaPath;
}
