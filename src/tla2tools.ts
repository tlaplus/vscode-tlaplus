import * as vscode from 'vscode';
import * as path from 'path';
import * as cp from 'child_process';
import * as fs from 'fs';
import { ChildProcess, spawn } from 'child_process';
import { pathToUri } from './common';
import { JavaVersionParser } from './parsers/javaVersion';

export const CFG_JAVA_HOME = 'tlaplus.java.home';

const NO_ERROR = 0;
const SYSTEM_ERROR = 255;           // Return code that means a problem with tooling
const MIN_TLA_ERROR = 10;           // Exit codes not related to tooling start from this number
const LOWEST_JAVA_VERSION = 8;
const javaCmd = 'java' + (process.platform === 'win32' ? '.exe' : '');
const toolsJarPath = path.resolve(__dirname, '../tools/tla2tools.jar');
const toolsBaseArgs: ReadonlyArray<string> = ['-XX:+UseParallelGC', '-cp', toolsJarPath];

let lastUsedJavaHome: string | undefined;
let cachedJavaPath: string | undefined;

/**
 * Thrown when there's some problem with Java or TLA+ tooling.
 */
export class ToolingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

export class JavaVersion {
    static UNKNOWN_VERSION = '?';

    constructor(
        readonly version: string,
        readonly fullOutput: string[]
    ) {}
}

/**
 * Executes a TLA+ tool.
 */
export async function runTool(toolName: string, filePath: string, toolArgs?: string[]): Promise<ChildProcess> {
    const javaPath = await obtainJavaPath();
    const args = toolsBaseArgs.slice(0);
    args.push(toolName);
    if (toolArgs) {
        toolArgs.forEach(arg => args.push(arg));
    }
    args.push(filePath);
    const proc = spawn(javaPath, args, { cwd: path.dirname(filePath) });
    addReturnCodeHandler(proc, toolName);
    return proc;
}

/**
 * Kills the given process.
 */
export function stopProcess(p: cp.ChildProcess) {
    if (!p.killed) {
        p.kill('SIGINT');
    }
}

export function reportBrokenToolchain(err: any) {
    console.log('Toolchain problem: ' + err.message);
    vscode.window.showErrorMessage('Toolchain is broken');
}

async function obtainJavaPath(): Promise<string> {
    const javaHome = vscode.workspace.getConfiguration().get<string>(CFG_JAVA_HOME);
    if (cachedJavaPath && javaHome === lastUsedJavaHome) {
        return cachedJavaPath;
    }
    const javaPath = buildJavaPath();
    cachedJavaPath = javaPath;
    lastUsedJavaHome = javaHome;
    await checkJavaVersion(javaPath);
    return javaPath;
}

/**
 * Builds path to the Java executable based on the configuration.
 */
function buildJavaPath(): string {
    let javaPath = javaCmd;
    const javaHome = vscode.workspace.getConfiguration().get<string>(CFG_JAVA_HOME);
    if (javaHome) {
        const homeUri = pathToUri(javaHome);
        javaPath = homeUri.fsPath + path.sep + 'bin' + path.sep + javaCmd;
        if (!fs.existsSync(javaPath)) {
            throw new ToolingError('Java executable not found. Check the Java Home configuration property.');
        }
    }
    return javaPath;
}

/**
 * Executes java -version and analyzes, if the version is 1.8 or higher.
 */
async function checkJavaVersion(javaPath: string) {
    const proc = spawn(javaPath, ['-version']);
    const parser = new JavaVersionParser(proc.stderr);
    const ver = await parser.readAll();
    if (ver.version === JavaVersion.UNKNOWN_VERSION) {
        console.debug('Java version output:');
        ver.fullOutput.forEach(line => console.debug(line));
        throw new ToolingError('Error while obtaining Java version. Check the Java Home configuration property.');
    }
    console.log(`Java version: ${ver.version}`);
    let num = ver.version;
    if (num.startsWith('1.')) {
        num = num.substring(2);
    }
    const pIdx = num.indexOf('.');
    if (pIdx > 0 && parseInt(num.substring(0, pIdx), 10) >= LOWEST_JAVA_VERSION) {
        return;
    }
    vscode.window.showWarningMessage(`Unexpected Java version: ${ver.version}`);
}

/**
 * Adds a handler to the given TLA+ tooling process that captures various system errors.
 */
function addReturnCodeHandler(proc: ChildProcess, toolName?: string) {
    proc.on('close', (exitCode) => {
        if (exitCode === NO_ERROR) {
            return;
        }
        if (exitCode === SYSTEM_ERROR || exitCode < MIN_TLA_ERROR) {
            vscode.window.showErrorMessage(`Error running ${toolName} (exit code ${exitCode})`);
        }
    });
}
