import { ChildProcess } from 'child_process';
import * as path from 'path';
import { Readable } from 'stream';
import * as vscode from 'vscode';
import { DCollection } from '../diagnostic';
import { tlcTraceToPuml } from '../generators/tlcTraceToPuml';
import { ModelCheckResult, ModelCheckResultSource, SpecFiles } from '../model/check';
import { ToolOutputChannel } from '../outputChannels';
import { showSequenceDiagramFromPuml } from '../panels/sequenceDiagramView';
import { TlcModelCheckerStdoutParser } from '../parsers/tlc';
import { saveStreamToFile } from '../outputSaver';
import { runTlc, stopProcess } from '../tla2tools';
import { ModelResolveMode, resolveModelForUri } from '../commands/modelResolver';

export type CheckSessionLifecycle = 'pending' | 'running' | 'completed' | 'failed' | 'cancelled';

export interface CheckRequest {
    showOptionsPrompt: boolean;
    showFullOutput?: boolean;
    extraOpts?: string[];
    extraJavaOpts?: string[];
    debuggerPortCallback?: (port?: number) => void;
}

const CFG_CREATE_OUT_FILES = 'tlaplus.tlc.modelChecker.createOutFiles';
const CFG_SEQ_DIAGRAM_TRACE_VAR = 'tlaplus.tlc.sequenceDiagram.traceVariable';

class Deferred<T> {
    readonly promise: Promise<T>;
    private resolveFn!: (value: T | PromiseLike<T>) => void;
    private rejectFn!: (reason?: unknown) => void;

    constructor() {
        this.promise = new Promise<T>((resolve, reject) => {
            this.resolveFn = resolve;
            this.rejectFn = reject;
        });
    }

    resolve(value: T): void {
        this.resolveFn(value);
    }

    reject(reason: unknown): void {
        this.rejectFn(reason);
    }
}

export class CheckSession {
    readonly id: string;
    readonly createdAt = new Date();
    readonly completion: Promise<ModelCheckResult | undefined>;

    private readonly completionDeferred = new Deferred<ModelCheckResult | undefined>();
    private readonly onDidChangeEmitter = new vscode.EventEmitter<CheckSession>();
    private _lifecycle: CheckSessionLifecycle = 'pending';
    private _process: ChildProcess | undefined;
    private _result: ModelCheckResult | undefined;
    private _diagnostics: DCollection | undefined;
    private _rawOutput = '';
    private _cancelRequested = false;

    readonly onDidChange = this.onDidChangeEmitter.event;

    constructor(
        readonly specFiles: SpecFiles,
        readonly request: CheckRequest
    ) {
        this.id = `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
        this.completion = this.completionDeferred.promise;
    }

    get lifecycle(): CheckSessionLifecycle {
        return this._lifecycle;
    }

    get process(): ChildProcess | undefined {
        return this._process;
    }

    get result(): ModelCheckResult | undefined {
        return this._result;
    }

    get diagnostics(): DCollection | undefined {
        return this._diagnostics;
    }

    get rawOutput(): string {
        return this._rawOutput;
    }

    get isActive(): boolean {
        return this._lifecycle === 'running' || this._lifecycle === 'pending';
    }

    begin(process: ChildProcess): void {
        this._process = process;
        this._lifecycle = 'running';
        this.fireDidChange();
    }

    appendRawOutput(chunk: string): void {
        this._rawOutput += chunk;
    }

    updateResult(result: ModelCheckResult): void {
        this._result = result;
        this.fireDidChange();
    }

    setDiagnostics(diagnostics: DCollection): void {
        this._diagnostics = diagnostics;
        this.fireDidChange();
    }

    finish(result: ModelCheckResult | undefined): void {
        this._result = result ?? this._result;
        this._lifecycle = this._cancelRequested || result?.stateName === 'Stopped'
            ? 'cancelled'
            : result?.stateName === 'Error'
                ? 'failed'
                : 'completed';
        this.fireDidChange();
        this.completionDeferred.resolve(this._result);
    }

    fail(error: unknown): void {
        this._lifecycle = this._cancelRequested ? 'cancelled' : 'failed';
        this.fireDidChange();
        this.completionDeferred.reject(error);
    }

    requestCancel(): void {
        this._cancelRequested = true;
        if (this._process) {
            stopProcess(this._process);
        }
    }

    private fireDidChange(): void {
        this.onDidChangeEmitter.fire(this);
    }
}

export class SessionRegistry {
    private readonly sessions = new Map<string, CheckSession>();
    private latestSessionId: string | undefined;

    add(session: CheckSession): void {
        this.sessions.set(session.id, session);
        this.latestSessionId = session.id;
    }

    get(sessionId: string): CheckSession | undefined {
        return this.sessions.get(sessionId);
    }

    list(): CheckSession[] {
        return Array.from(this.sessions.values());
    }

    latest(): CheckSession | undefined {
        return this.latestSessionId ? this.sessions.get(this.latestSessionId) : undefined;
    }

    latestCompleted(): CheckSession | undefined {
        return this.list()
            .filter((session) => !session.isActive)
            .sort((left, right) => right.createdAt.getTime() - left.createdAt.getTime())[0];
    }

    latestActive(predicate?: (session: CheckSession) => boolean): CheckSession | undefined {
        return this.list()
            .filter((session) => session.isActive)
            .filter((session) => predicate ? predicate(session) : true)
            .sort((left, right) => right.createdAt.getTime() - left.createdAt.getTime())[0];
    }

    active(): CheckSession[] {
        return this.list().filter((session) => session.isActive);
    }

    lastSpecFiles(): SpecFiles | undefined {
        return this.latest()?.specFiles;
    }
}

export class CheckService implements vscode.Disposable {
    readonly sessions = new SessionRegistry();
    readonly outputChannel = new ToolOutputChannel('TLC', mapTlcOutputLine);

    private readonly onDidStartSessionEmitter = new vscode.EventEmitter<CheckSession>();
    private readonly onDidUpdateSessionEmitter = new vscode.EventEmitter<CheckSession>();
    private readonly onDidFinishSessionEmitter = new vscode.EventEmitter<CheckSession>();
    private readonly disposables: vscode.Disposable[] = [
        this.onDidStartSessionEmitter,
        this.onDidUpdateSessionEmitter,
        this.onDidFinishSessionEmitter,
    ];

    readonly onDidStartSession = this.onDidStartSessionEmitter.event;
    readonly onDidUpdateSession = this.onDidUpdateSessionEmitter.event;
    readonly onDidFinishSession = this.onDidFinishSessionEmitter.event;

    async resolveSpecFiles(
        fileUri: vscode.Uri,
        warn = true,
        interactive = true,
        mode: ModelResolveMode = 'adjacent'
    ): Promise<SpecFiles | undefined> {
        const resolved = await resolveModelForUri(fileUri, warn, interactive, mode);
        if (!resolved) {
            return undefined;
        }
        return new SpecFiles(
            resolved.tlaPath,
            resolved.cfgPath,
            resolved.modelName,
            resolved.outputDir
        );
    }

    async startSession(specFiles: SpecFiles, request: CheckRequest): Promise<CheckSession | undefined> {
        const procInfo = await runTlc(
            specFiles.tlaFilePath,
            specFiles.cfgFilePath,
            request.showOptionsPrompt,
            request.extraOpts ?? [],
            request.extraJavaOpts ?? []
        );
        if (!procInfo) {
            return undefined;
        }

        const session = new CheckSession(specFiles, request);
        session.onDidChange(() => this.onDidUpdateSessionEmitter.fire(session));
        this.sessions.add(session);
        this.outputChannel.bindTo(procInfo);
        session.begin(procInfo.process);
        this.onDidStartSessionEmitter.fire(session);

        procInfo.process.on('close', () => {
            if (session.isActive) {
                session.finish(session.result);
                this.onDidFinishSessionEmitter.fire(session);
            }
        });

        if (procInfo.process.stdout) {
            procInfo.process.stdout.on('data', (chunk: Buffer | string) => {
                session.appendRawOutput(String(chunk));
            });
        }

        this.attachFileSaver(specFiles, procInfo.process);
        void this.consumeSessionOutput(session, procInfo.process.stdout, request.debuggerPortCallback)
            .catch((error) => {
                session.fail(error);
                this.onDidFinishSessionEmitter.fire(session);
            });
        return session;
    }

    async runToCompletion(specFiles: SpecFiles, request: CheckRequest): Promise<CheckSession | undefined> {
        const session = await this.startSession(specFiles, request);
        if (!session) {
            return undefined;
        }
        await session.completion;
        return session;
    }

    stopLatestSession(predicate?: (session: CheckSession) => boolean): boolean {
        const session = this.sessions.latestActive(predicate);
        if (!session) {
            return false;
        }
        session.requestCancel();
        return true;
    }

    latestSession(): CheckSession | undefined {
        return this.sessions.latest();
    }

    latestCompletedSession(): CheckSession | undefined {
        return this.sessions.latestCompleted();
    }

    revealOutput(): void {
        this.outputChannel.revealWindow();
    }

    async maybeGenerateSequenceDiagram(
        session: CheckSession,
        extContext: vscode.ExtensionContext
    ): Promise<void> {
        try {
            const traceVar = vscode.workspace.getConfiguration()
                .get<string>(CFG_SEQ_DIAGRAM_TRACE_VAR) ?? '_seqDiagramTrace';
            const puml = tlcTraceToPuml(session.rawOutput, {
                traceVariable: traceVar,
                title: session.specFiles.modelName,
            });
            if (!puml) {
                return;
            }
            await showSequenceDiagramFromPuml(puml, extContext, session.specFiles.modelName);
        } catch (error) {
            this.outputChannel.appendLine(`[Sequence Diagram] Failed to generate: ${error}`);
        }
    }

    dispose(): void {
        this.sessions.active().forEach((session) => session.requestCancel());
        this.disposables.forEach((disposable) => disposable.dispose());
    }

    private async consumeSessionOutput(
        session: CheckSession,
        stdout: Readable | null,
        debuggerPortCallback?: (port?: number) => void
    ): Promise<void> {
        const stdoutParser = new TlcModelCheckerStdoutParser(
            ModelCheckResultSource.Process,
            stdout,
            session.specFiles,
            session.request.showFullOutput ?? true,
            (checkResult) => session.updateResult(checkResult),
            debuggerPortCallback
        );
        const diagnostics = await stdoutParser.readAll();
        session.setDiagnostics(diagnostics);
        session.finish(session.result);
        this.onDidFinishSessionEmitter.fire(session);
    }

    private attachFileSaver(specFiles: SpecFiles, proc: ChildProcess): void {
        const createOutFiles = vscode.workspace.getConfiguration().get<boolean>(CFG_CREATE_OUT_FILES);
        if (typeof createOutFiles === 'undefined' || createOutFiles) {
            const outFilePath = path.join(specFiles.outputDir, `${specFiles.modelName}.out`);
            saveStreamToFile(proc.stdout, outFilePath);
        }
    }
}

export function mapTlcOutputLine(line: string): string | undefined {
    if (line === '') {
        return line;
    }
    const cleanLine = line.replace(/@!@!@(START|END)MSG \d+(:\d+)? @!@!@/g, '');
    return cleanLine === '' ? undefined : cleanLine;
}
