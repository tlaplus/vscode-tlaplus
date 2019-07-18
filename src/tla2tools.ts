import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import * as cp from 'child_process';
import { Readable } from 'stream';
import { DCollection } from './diagnostic';

const toolsJarPath = path.resolve(__dirname, '../tools/tla2tools.jar');
const javaCmd = 'java' + (process.platform === 'win32' ? '.exe' : '');

export class ToolingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

/**
 * Auxiliary class that reads chunks from the given stream, breaks data into lines
 * and sends them to the parsing method line by line.
 */
export abstract class ProcessOutputParser {
    closed: boolean = false;
    buf: string | null = null;
    resolve?: (result: DCollection) => void;
    dCol: DCollection = new DCollection();
    protected readonly filePath?: string;

    constructor(stream: Readable, filePath?: string) {
        this.filePath = filePath;
        const me = this;
        stream.on('data', chunk => me.handleData(chunk));
        stream.on('close', () => me.handleData(null));
        if (filePath) {
            this.addDiagnosticFilePath(filePath);
        }
    }

    /**
     * Reads the stream to the end, parsing all the lines.
     */
    async readAll(): Promise<DCollection> {
        const me = this;
        return new Promise(resolve => {
            me.resolve = resolve;
        });
    }

    protected abstract parseLine(line: string | null): void;

    protected addDiagnosticFilePath(filePath: string) {
        this.dCol.addFilePath(filePath);
    }

    protected addDiagnosticMessage(filePath: string, range: vscode.Range, text: string) {
        this.dCol.addMessage(filePath, range, text);
    }

    private handleData(chunk: Buffer | string | null) {
        if (this.closed) {
            throw new Error('Stream is closed.');
        }
        if (chunk === null) {
            this.parseLine(this.buf);
            this.buf = null;
            this.closed = true;
            if (this.resolve) {
                this.resolve(this.dCol);
            }
            return;
        }
        const str = String(chunk);
        const eChunk = this.buf === null ? str : this.buf + str;
        const lines = eChunk.split('\n');
        if (str.endsWith('\n')) {
            this.buf = null;
            lines.pop();
        } else {
            this.buf = lines.pop() || null;
        }
        const me = this;
        lines.forEach(l => me.parseLine(l));
    }
}

/**
 * Executes a Java process.
 */
export function runTool(
    toolName: string,
    filePath: string,
    toolArgs?: string[],
    token?: vscode.CancellationToken
): cp.ChildProcess {
    const javaPath = buildJavaPath();
    let p: cp.ChildProcess;
    if (token) {
        token.onCancellationRequested(() => {
            if (p) {
                killProcessTree(p.pid);
            }
        });
    }
    const eArgs = ['-XX:+UseParallelGC', '-cp', toolsJarPath, toolName].concat(toolArgs || []);
    eArgs.push(filePath);
    return cp.spawn(javaPath, eArgs, { cwd: path.dirname(filePath) });
}

export function reportBrokenToolchain(err: any) {
    console.log('Toolchain problem: ' + err.message);
    vscode.window.showErrorMessage('Toolchain is broken');
}

function buildJavaPath(): string {
    const javaHome = vscode.workspace.getConfiguration().get<string>('tlaplus.java.home');
    let javaPath = javaCmd;
    if (javaHome) {
        const homeUri = vscode.Uri.parse('file://' + javaHome);
        const javaPath = homeUri.fsPath + path.sep + 'bin' + path.sep + javaCmd;
        if (!fs.existsSync(javaPath)) {
            throw new ToolingError('Java command not found. Check the Java Home configuration property.');
        }
    }
    return javaPath;
}

function killProcessTree(processId: number): void {
    if (process.platform === 'win32') {
        const TASK_KILL = 'C:\\Windows\\System32\\taskkill.exe';
        // when killing a process in Windows its child processes are *not* killed but become root processes.
        // Therefore we use TASKKILL.EXE
        try {
            cp.execSync(`${TASK_KILL} /F /T /PID ${processId}`);
        } catch (err) {
        }
    } else {
        // on linux and OS X we kill all direct and indirect child processes as well
        try {
            const cmd = path.join(__dirname, '../../../scripts/terminateProcess.sh');
            cp.spawnSync(cmd, [processId.toString()]);
        } catch (err) {
        }
    }
}