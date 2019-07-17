import { ProcessOutputParser } from "../tla2tools";
import { Readable } from "stream";

export enum CheckStatus {
    NotStarted,
    Started,
    SanyInProgress,
    SanyFinished,
    InitialStatesComputing,
    InitialStatesComputed,
    Finished
}

// TLC message types
const NO_TYPE = -1;
const TLC_UNKNOWN = -2;
const TLC_MODE_MC = 2187;
const TLC_SANY_START = 2220;
const TLC_SANY_END = 2219;
const TLC_COMPUTING_INIT = 2189;
const TLC_COMPUTING_INIT_PROGRESS = 2269;
const TLC_INIT_GENERATED1 = 2190;
const TLC_INIT_GENERATED2 = 2191;
const TLC_INIT_GENERATED3 = 2207;
const TLC_INIT_GENERATED4 = 2208;
const TLC_FINISHED = 2186;

/**
 * A state of a process in a particular moment of time.
 */
export class State {
    readonly title: string;
    readonly variables: string[];

    constructor(title: string, variables: string[]) {
        this.title = title;
        this.variables = variables;
    }
}

/**
 * Represents the state of a TLA model checking process.
 */
export class ModelCheckResult {
    private status: CheckStatus = CheckStatus.NotStarted;
    private processInfo: string | null = null;
    private errorTrace: State[] | null = null;
    private msgType: number = NO_TYPE;
    private msgBuffer: string[] = [];

    getStatus(): CheckStatus {
        return this.status;
    }

    getProcessInfo(): string | null {
        return this.processInfo;
    }

    addLine(line: string) {
        if (this.msgType === NO_TYPE) {
            this.msgType = this.tryParseMessageStart(line);
        } else if (this.tryParseMessageEnd(line)) {
            this.handleMessageEnd();
        } else {
            this.msgBuffer.push(line);
        }
    }

    private handleMessageEnd() {
        if (this.status === CheckStatus.NotStarted) {
            this.status = CheckStatus.Started;
        }
        switch (this.msgType) {
            case TLC_MODE_MC:
                this.processInfo = this.msgBuffer.join('');
                break;
            case TLC_SANY_START:
                this.status = CheckStatus.SanyInProgress;
                break;
            case TLC_SANY_END:
                this.status = CheckStatus.SanyFinished;
                break;
            case TLC_COMPUTING_INIT:
                this.status = CheckStatus.InitialStatesComputing;
                break;
            case TLC_COMPUTING_INIT_PROGRESS:
                this.status = CheckStatus.InitialStatesComputing;
                break;
            case TLC_INIT_GENERATED1:
            case TLC_INIT_GENERATED2:
            case TLC_INIT_GENERATED3:
            case TLC_INIT_GENERATED4:
                this.status = CheckStatus.InitialStatesComputed;
                break;
            case TLC_FINISHED:
                this.status = CheckStatus.Finished;
                break;
            }
        this.msgType = NO_TYPE;
        this.msgBuffer.length = 0;
    }

    private tryParseMessageStart(line: string): number {
        if (!line.startsWith('@!@!@STARTMSG ') || !line.endsWith(' @!@!@')) {
            return NO_TYPE;
        }
        const eLine = line.substring(14, line.length - 6);
        const parts = eLine.split(':');
        if (parts.length > 0) {
            return parseInt(parts[0]);
        }
        return TLC_UNKNOWN;
    }

    private tryParseMessageEnd(line: string): boolean {
        return line.startsWith('@!@!@ENDMSG ') && line.endsWith(' @!@!@');
    }
}

/**
 * Parses stdout of TLC model checker.
 */
export class TLCModelCheckerStdoutParser extends ProcessOutputParser {
    checkResult = new ModelCheckResult();
    handler: (checkResult: ModelCheckResult) => void;

    constructor(stdout: Readable, filePath: string, handler: (checkResult: ModelCheckResult) => void) {
        super(stdout, filePath);
        this.handler = handler;
    }

    protected parseLine(line: string | null) {
        console.log('tlc> ' + (line === null ? ':END:' : line));
        if (line !== null) {
            this.checkResult.addLine(line);
            this.handler(this.checkResult);
        }
    }
}
