import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import * as cp from 'child_process';
import { Readable } from 'stream';
import { DCollection } from './diagnostic';
import { pathToUri, ParsingError } from './common';

const toolsJarPath = path.resolve(__dirname, '../tools/tla2tools.jar');
const killProcessScriptPath = path.resolve(__dirname, '../tools/kill_process.sh');
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
    lines: string[] | undefined;

    protected readonly filePath?: string;

    constructor(source: Readable | string[], filePath?: string) {
        this.filePath = filePath;
        if (source instanceof Readable) {
            const me = this;
            source.on('data', chunk => me.handleData(chunk));
            source.on('end', () => me.handleData(null));
        } else {
            this.lines = source;
        }
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

    /**
     * Parses the source synchronously.
     * For this method to work, the source of the lines must be an array of l.
     */
    readAllSync(): DCollection {
        if (!this.lines) {
            throw new ParsingError('Cannot parse synchronously because the source is not a set of lines');
        }
        this.lines.forEach(l => {
            this.tryParseLine(l);
        });
        return this.dCol;
    }

    protected abstract parseLine(line: string | null): void;

    protected handleError(err: any) {
        // Do nothing by default
    }

    protected addDiagnosticFilePath(filePath: string) {
        this.dCol.addFilePath(filePath);
    }

    protected addDiagnosticMessage(filePath: string, range: vscode.Range, text: string) {
        this.dCol.addMessage(filePath, range, text);
    }

    protected addDiagnosticCollection(dCol: DCollection) {
        dCol.getFilePaths().forEach(fp => this.addDiagnosticFilePath(fp));
        dCol.getMessages().forEach(m => this.dCol.addMessage(m.filePath, m.diagnostic.range, m.diagnostic.message));
    }

    private handleData(chunk: Buffer | string | null) {
        if (this.closed) {
            throw new Error('Stream is closed.');
        }
        if (chunk === null) {
            console.log(':END:');
            this.tryParseLine(this.buf);
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
        lines.forEach(line => {
            console.log('> ' + line);
            me.tryParseLine(line);
        });
    }

    private tryParseLine(line: string | null) {
        try {
            this.parseLine(line);
        } catch (err) {
            this.handleError(err);
            console.log(`Error parsing output line: ${err}`);
        }
    }
}

/**
 * Executes a Java process.
 */
export function runTool(
    toolName: string,
    filePath: string,
    toolArgs?: string[]
): cp.ChildProcess {
    const javaPath = buildJavaPath();
    const eArgs = ['-XX:+UseParallelGC', '-cp', toolsJarPath, toolName].concat(toolArgs || []);
    eArgs.push(filePath);
    return cp.spawn(javaPath, eArgs, { cwd: path.dirname(filePath) });
}

/**
 * Kills the given process.
 */
export function stopProcess(p: cp.ChildProcess) {
    console.log(`Stopping process #${p.pid}...`);
    if (process.platform === 'win32') {
        const TASK_KILL = 'C:\\Windows\\System32\\taskkill.exe';
        // when killing a process in Windows its child processes are *not* killed but become root processes.
        // Therefore we use TASKKILL.EXE
        try {
            cp.execSync(`${TASK_KILL} /F /T /PID ${p.pid}`);
        } catch (err) {
            console.log('Error killing Windows process: ' + err);
        }
    } else {
        // on linux and OS X we kill all direct and indirect child processes as well
        try {
            const res = cp.spawnSync(killProcessScriptPath, [p.pid.toString()]);
            if (res.error) {
                throw res.error;
            }
        } catch (err) {
            console.log('Error killing Unix process: ' + err);
        }
    }
}

export function reportBrokenToolchain(err: any) {
    console.log('Toolchain problem: ' + err.message);
    vscode.window.showErrorMessage('Toolchain is broken');
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
