import { Range } from 'vscode';
import { ProcessOutputParser } from "../tla2tools";
import { Readable } from "stream";


const STATUS_EMIT_TIMEOUT = 500;    // msec

const STATE_RUNNING = 'R';
const STATE_SUCCESS = 'S';
const STATE_ERROR = 'E';

export enum CheckStatus {
    NotStarted,
    Started,
    SanyParsing,
    SanyFinished,
    InitialStatesComputing,
    InitialStatesComputed,
    TemporalPropertiesChecking,
    TemporalPropertiesChecked,
    Finished
}

export const STATUS_NAMES = new Map<CheckStatus, string>();
STATUS_NAMES.set(CheckStatus.NotStarted, 'Not started');
STATUS_NAMES.set(CheckStatus.Started, 'Started');
STATUS_NAMES.set(CheckStatus.SanyParsing, 'SANY parsing');
STATUS_NAMES.set(CheckStatus.SanyFinished, 'SANY finished');
STATUS_NAMES.set(CheckStatus.InitialStatesComputing, 'Computing initial states');
STATUS_NAMES.set(CheckStatus.InitialStatesComputed, 'Initial states computed');
STATUS_NAMES.set(CheckStatus.TemporalPropertiesChecking, 'Checking temporal properties');
STATUS_NAMES.set(CheckStatus.TemporalPropertiesChecked, 'Temporal properties checked');
STATUS_NAMES.set(CheckStatus.Finished, 'Finished');

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
const TLC_CHECKING_TEMPORAL_PROPS = 2192;
const TLC_CHECKING_TEMPORAL_PROPS_END = 2267;
const TLC_COVERAGE_NEXT = 2772;
const TLC_COVERAGE_INIT = 2773;
const TLC_PROGRESS_STATS = 2200;
const TLC_TEMPORAL_PROPERTY_VIOLATED = 2116;
const TLC_INITIAL_STATE = 2102;
const TLC_NESTED_EXPRESSION = 2103;
const TLC_FINISHED = 2186;
const TLC_SUCCESS = 2193;

/**
 * Statistics on initial state generation.
 */
export class InitialStateStatItem {
    readonly time: string;
    readonly diameter: number;
    readonly total: number;
    readonly distinct: number;
    readonly queueSize: number;

    constructor(time: string, diameter: number, total: number, distinct: number, queueSize: number) {
        this.time = time;
        this.diameter = diameter;
        this.total = total;
        this.distinct = distinct;
        this.queueSize = queueSize;
    }
}

/**
 * Statistics on coverage.
 */
export class CoverageItem {
    readonly module: string;
    readonly action: string;
    readonly location: Range;
    readonly total: number;
    readonly distinct: number;

    constructor(module: string, action: string, location: Range, total: number, distinct: number) {
        this.module = module;
        this.action = action;
        this.location = location;
        this.total = total;
        this.distinct = distinct;
    }
}

/**
 * A state of a process in a particular moment of time.
 */
export class ErrorTraceItem {
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
    readonly state: string;
    readonly success: boolean;
    readonly status: CheckStatus;
    readonly statusName: string;
    readonly processInfo: string | null;
    readonly initialStatesStat: InitialStateStatItem[];
    readonly coverageStat: CoverageItem[];
    readonly errors: string[][];
    readonly errorTrace: ErrorTraceItem[];

    constructor(
        success: boolean,
        status: CheckStatus,
        processInfo: string | null,
        initialStatesStat: InitialStateStatItem[],
        coverageStat: CoverageItem[],
        errors: string[][],
        errorTrace: ErrorTraceItem[]
    ) {
        if (status === CheckStatus.Finished) {
            this.state = success ? STATE_SUCCESS : STATE_ERROR;
        } else {
            this.state = STATE_RUNNING;
        }
        this.success = success;
        this.status = status;
        this.statusName = STATUS_NAMES.get(status) || 'Working';
        this.processInfo = processInfo;
        this.initialStatesStat = initialStatesStat;
        this.coverageStat = coverageStat;
        this.errors = errors;
        this.errorTrace = errorTrace;
    }
}

/**
 * Gradually builds ModelCheckResult by processing TLC output lines.
 */
class ModelCheckResultBuilder {
    private success: boolean = false;
    private status: CheckStatus = CheckStatus.NotStarted;
    private processInfo: string | null = null;
    private initialStatesStat: InitialStateStatItem[] = [];
    private coverageStat: CoverageItem[] = [];
    private errors: string[][] = [];
    private errorTrace: ErrorTraceItem[] = [];
    private msgType: number = NO_TYPE;
    private msgBuffer: string[] = [];

    getStatus(): CheckStatus {
        return this.status;
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

    build(): ModelCheckResult {
        return new ModelCheckResult(
            this.success,
            this.status,
            this.processInfo,
            this.initialStatesStat,
            this.coverageStat,
            this.errors,
            this.errorTrace
        );
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
                this.status = CheckStatus.SanyParsing;
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
                this.parseInitialStatesComputed();
                break;
            case TLC_CHECKING_TEMPORAL_PROPS:
                this.status = CheckStatus.TemporalPropertiesChecking;
                break;
            case TLC_CHECKING_TEMPORAL_PROPS_END:
                this.status = CheckStatus.TemporalPropertiesChecked;
                break;
            case TLC_PROGRESS_STATS:
                this.parseProgressStats();
                break;
            case TLC_COVERAGE_INIT:
                this.coverageStat.length = 0;
                this.parseCoverage();
                break;
            case TLC_COVERAGE_NEXT:
                this.parseCoverage();
                break;
            case TLC_INITIAL_STATE:
            case TLC_NESTED_EXPRESSION:
            case TLC_TEMPORAL_PROPERTY_VIOLATED:
                this.errors.push(this.msgBuffer.slice(0));
                break;
            case TLC_SUCCESS:
                this.success = true;
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

    private parseInitialStatesComputed() {
        const matches = this.tryMatchBufferLine(/^Finished computing initial states: (\d+) distinct states generated at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}).*$/g);
        if (matches) {
            const count = parseInt(matches[1]);
            this.initialStatesStat.push(new InitialStateStatItem(matches[2], 0, count, count, count));
        }
    }

    private parseProgressStats() {
        const matches = this.tryMatchBufferLine(/^Progress\(([\d,]+)\) at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}): ([\d,]+) states generated.*, ([\d,]+) distinct states found.*, ([\d,]+) states left on queue.*/g);
        if (matches) {
            this.initialStatesStat.push(new InitialStateStatItem(
                matches[2],
                parseIntWithComma(matches[1]),
                parseIntWithComma(matches[3]),
                parseIntWithComma(matches[4]),
                parseIntWithComma(matches[5])
            ));
        }
    }

    private parseCoverage() {
        const matches = this.tryMatchBufferLine(/^<([a-zA-Z0-9_]+) line (\d+), col (\d+) to line (\d+), col (\d+) of module ([a-zA-Z0-9_]+)>: (\d+):(\d+)/g);
        if (matches) {
            this.coverageStat.push(new CoverageItem(
                matches[6],
                matches[1],
                new Range(
                    parseInt(matches[2]),
                    parseInt(matches[3]),
                    parseInt(matches[4]),
                    parseInt(matches[5])
                ),
                parseInt(matches[7]),
                parseInt(matches[8])
            ));
            const name = matches[1];
            const fromLine = parseInt(matches[2]);
            const fromCol = parseInt(matches[3]);
            const toLine = parseInt(matches[4]);
            const toCol = parseInt(matches[5]);
            const module = matches[6];
            const total = parseInt(matches[7]);
            const distinct = parseInt(matches[8]);
        }
    }

    private tryMatchBufferLine(regExp: RegExp): RegExpExecArray | null {
        if (this.msgBuffer.length === 0) {
            return null;
        }
        return regExp.exec(this.msgBuffer[0]);
    }
}

/**
 * Parses stdout of TLC model checker.
 */
export class TLCModelCheckerStdoutParser extends ProcessOutputParser {
    checkResultBuilder = new ModelCheckResultBuilder();
    handler: (checkResult: ModelCheckResult) => void;
    timer: NodeJS.Timer | undefined = undefined;
    first: boolean = true;

    constructor(stdout: Readable, filePath: string, handler: (checkResult: ModelCheckResult) => void) {
        super(stdout, filePath);
        this.handler = handler;
    }

    protected parseLine(line: string | null) {
        console.log('tlc> ' + (line === null ? ':END:' : line));
        if (line !== null) {
            this.checkResultBuilder.addLine(line);
            this.scheduleUpdate();
        }
    }

    private scheduleUpdate() {
        if (this.timer) {
            return;
        }
        let timeout = STATUS_EMIT_TIMEOUT;
        if (this.first && this.checkResultBuilder.getStatus() !== CheckStatus.NotStarted) {
            // First status change, show immediately
            this.first = false;
            timeout = 0;
        }
        const me = this;
        this.timer = setTimeout(() => {
            me.handler(me.checkResultBuilder.build());
            me.timer = undefined;
        }, timeout);
    }
}

function parseIntWithComma(str: string): number {
    const c = str.split(',').join('');
    return parseInt(c);
}