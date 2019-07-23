import { Range } from 'vscode';
import { ProcessOutputParser } from '../tla2tools';
import { Readable } from 'stream';
import { CheckStatus, ModelCheckResult, InitialStateStatItem, CoverageItem, ErrorTraceItem,
    VariableValue } from '../model/check';
import { parseValueLines } from './tlcValues';
import { SanyStdoutParser } from './sany';
import { DCollection } from '../diagnostic';
import { pathToModuleName, parseDateTime } from '../common';
import * as moment from 'moment/moment';

const STATUS_EMIT_TIMEOUT = 500;    // msec

// TLC message types
const NO_TYPE = -1;
const TLC_UNKNOWN = -2;
const GENERAL = 1000;
const TLC_MODE_MC = 2187;
const TLC_SANY_START = 2220;
const TLC_SANY_END = 2219;
const TLC_CHECKPOINT_START = 2195;
const TLC_STARTING = 2185;
const TLC_COMPUTING_INIT = 2189;
const TLC_COMPUTING_INIT_PROGRESS = 2269;
const TLC_INIT_GENERATED1 = 2190;
const TLC_INIT_GENERATED2 = 2191;
const TLC_INIT_GENERATED3 = 2207;
const TLC_INIT_GENERATED4 = 2208;
const TLC_CHECKING_TEMPORAL_PROPS = 2192;
const TLC_DISTRIBUTED_SERVER_RUNNING = 7000;
const TLC_DISTRIBUTED_WORKER_REGISTERED = 7001;
const TLC_DISTRIBUTED_WORKER_DEREGISTERED = 7002;
const TLC_COVERAGE_NEXT = 2772;
const TLC_COVERAGE_INIT = 2773;
const TLC_PROGRESS_STATS = 2200;
const TLC_TEMPORAL_PROPERTY_VIOLATED = 2116;
const TLC_INITIAL_STATE = 2102;
const TLC_NESTED_EXPRESSION = 2103;
const TLC_VALUE_ASSERT_FAILED = 2132;
const TLC_STATE_PRINT1 = 2216;
const TLC_STATE_PRINT2 = 2217;
const TLC_STATE_PRINT3 = 2218;
const TLC_FINISHED = 2186;
const TLC_SUCCESS = 2193;

/**
 * Parses stdout of TLC model checker.
 */
export class TLCModelCheckerStdoutParser extends ProcessOutputParser {
    checkResultBuilder: ModelCheckResultBuilder;
    handler: (checkResult: ModelCheckResult) => void;
    timer: NodeJS.Timer | undefined = undefined;
    first: boolean = true;

    constructor(stdout: Readable, filePath: string, handler: (checkResult: ModelCheckResult) => void) {
        super(stdout, filePath);
        this.handler = handler;
        const moduleName = pathToModuleName(filePath);
        this.checkResultBuilder = new ModelCheckResultBuilder(moduleName);
    }

    protected parseLine(line: string | null) {
        if (line !== null) {
            this.checkResultBuilder.addLine(line);
            this.scheduleUpdate();
        } else {
            // Copy SANY messages
            const dCol = this.checkResultBuilder.getSanyMessages();
            if (dCol) {
                this.addDiagnosticCollection(dCol);
            }
        }
    }

    protected handleError(err: any) {
        this.checkResultBuilder.handleError(err);
        this.scheduleUpdate();
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

/**
 * Gradually builds ModelCheckResult by processing TLC output lines.
 */
class ModelCheckResultBuilder {
    private modelName: string;
    private success: boolean = false;
    private status: CheckStatus = CheckStatus.NotStarted;
    private startDateTime: moment.Moment | undefined;
    private endDateTime: moment.Moment | undefined;
    private duration: number | undefined;       // msec
    private processInfo: string | null = null;
    private initialStatesStat: InitialStateStatItem[] = [];
    private coverageStat: CoverageItem[] = [];
    private errors: string[][] = [];
    private errorTrace: ErrorTraceItem[] = [];
    private msgType: number = NO_TYPE;
    private msgBuffer: string[] = [];
    private sanyBuffer: string[] = [];
    private sanyMessages: DCollection | undefined;
    private workersCount: number = 0;
    private firstStatTime: moment.Moment | undefined;

    constructor(modelName: string) {
        this.modelName = modelName;
    }

    getStatus(): CheckStatus {
        return this.status;
    }

    getSanyMessages(): DCollection | undefined {
        return this.sanyMessages;
    }

    addLine(line: string) {
        if (this.msgType === NO_TYPE) {
            this.msgType = this.tryParseMessageStart(line);
            if (this.msgType === NO_TYPE && this.status === CheckStatus.SanyParsing) {
                this.sanyBuffer.push(line);
            }
        } else if (this.tryParseMessageEnd(line)) {
            this.handleMessageEnd();
        } else if (line !== '') {
            this.msgBuffer.push(line);
        }
    }

    handleError(_: any) {
        this.resetMessage();
    }

    build(): ModelCheckResult {
        return new ModelCheckResult(
            this.modelName,
            this.success,
            this.status,
            this.processInfo,
            this.initialStatesStat,
            this.coverageStat,
            this.errors,
            this.errorTrace,
            this.sanyMessages,
            this.startDateTime,
            this.endDateTime,
            this.duration,
            this.workersCount
        );
    }

    private handleMessageEnd() {
        if (this.status === CheckStatus.NotStarted) {
            this.status = CheckStatus.Starting;
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
                this.parseSanyOutput();
                break;
            case TLC_CHECKPOINT_START:
                this.status = CheckStatus.Checkpointing;
                break;
            case TLC_STARTING:
                this.parseStarting();
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
                this.parseInitialStatesComputed();
                break;
            case TLC_CHECKING_TEMPORAL_PROPS:
                if (this.msgBuffer.length > 0 && this.msgBuffer[0].indexOf('complete') >= 0) {
                    this.status = CheckStatus.CheckingLivenessFinal;
                } else {
                    this.status = CheckStatus.CheckingLiveness;
                }
                break;
            case TLC_DISTRIBUTED_SERVER_RUNNING:
                this.status = CheckStatus.ServerRunning;
                break;
            case TLC_DISTRIBUTED_WORKER_REGISTERED:
                this.status = CheckStatus.WorkersRegistered;
                this.workersCount += 1;
                break;
            case TLC_DISTRIBUTED_WORKER_DEREGISTERED:
                this.workersCount -= 1;
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
            case GENERAL:
            case TLC_INITIAL_STATE:
            case TLC_NESTED_EXPRESSION:
            case TLC_TEMPORAL_PROPERTY_VIOLATED:
            case TLC_VALUE_ASSERT_FAILED:
                this.errors.push(this.msgBuffer.slice(0));
                break;
            case TLC_STATE_PRINT1:
            case TLC_STATE_PRINT2:
            case TLC_STATE_PRINT3:
                this.parseErrorTraceItem();
                break;
            case TLC_SUCCESS:
                this.success = true;
                break;
            case TLC_FINISHED:
                this.status = CheckStatus.Finished;
                this.parseFinished();
                break;
        }
        this.resetMessage();
    }

    private resetMessage() {
        this.msgType = NO_TYPE;
        this.msgBuffer.length = 0;
    }

    // TODO: Sometimes messages start not on the new line: ""
    // tlc> @!@!@STARTMSG 1000:1 @!@!@
    // tlc> TLC threw an unexpected exception.
    // tlc> This was probably caused by an error in the spec or model.
    // tlc> See the User Output or TLC Console for clues to what happened.
    // tlc> The exception was a tlc2.tool.EvalException
    // tlc> : @!@!@STARTMSG 2132:0 @!@!@    <--------------------------- Here!
    // tlc> The first argument of Assert evaluated to FALSE; the second argument was:
    // tlc> "Failure of assertion at line 43, column 3."
    // tlc> @!@!@ENDMSG 2132 @!@!@
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

    private parseStarting() {
        const matches = this.tryMatchBufferLine(/^Starting\.\.\. \((\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\)$/g);
        if (matches) {
            this.startDateTime = parseDateTime(matches[1]);
        }
    }

    private parseFinished() {
        const matches = this.tryMatchBufferLine(/^Finished in (\d+)ms at \((\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\)$/g);
        if (matches) {
            this.duration = parseInt(matches[1]);
            this.endDateTime = parseDateTime(matches[2]);
        }
    }

    private parseSanyOutput() {
        const sany = new SanyStdoutParser(this.sanyBuffer);
        this.sanyMessages = sany.readAllSync();
        this.sanyBuffer = [];
    }

    private parseInitialStatesComputed() {
        const matches = this.tryMatchBufferLine(/^Finished computing initial states: (\d+) distinct states generated at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}).*$/g);
        if (matches) {
            const count = parseInt(matches[1]);
            this.firstStatTime = parseDateTime(matches[2]);
            this.initialStatesStat.push(new InitialStateStatItem('00:00:00', 0, count, count, count));
        }
    }

    private parseProgressStats() {
        const matches = this.tryMatchBufferLine(/^Progress\(([\d,]+)\) at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}): ([\d,]+) states generated.*, ([\d,]+) distinct states found.*, ([\d,]+) states left on queue.*/g);
        if (matches) {
            this.initialStatesStat.push(new InitialStateStatItem(
                this.calcTimestamp(matches[2]),
                parseIntWithComma(matches[1]),
                parseIntWithComma(matches[3]),
                parseIntWithComma(matches[4]),
                parseIntWithComma(matches[5])
            ));
        }
    }

    private parseCoverage() {
        const matches = this.tryMatchBufferLine(/^<(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>: (\d+):(\d+)/g);
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
        }
    }

    private parseErrorTraceItem() {
        if (this.msgBuffer.length === 0) {
            console.log('Error trace expected but message buffer is empty');
            return;
        }
        // Try special cases like <Initial predicate>, <Stuttering>, etc.
        const sMatches = this.tryMatchBufferLine(/^(\d+): <([\w\s]+)>$/g);
        if (sMatches) {
            this.errorTrace.push(new ErrorTraceItem(
                parseInt(sMatches[1]),
                sMatches[2],
                '', '', new Range(0, 0, 0, 0), this.parseErrorTraceVariables()));
            return;
        }
        // Otherwise fall back to simple states
        const matches = this.tryMatchBufferLine(/^(\d+): <(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>$/g);
        if (!matches) {
            return;
        }
        this.errorTrace.push(new ErrorTraceItem(
            parseInt(matches[1]),
            `${matches[2]} in ${matches[7]}`,
            matches[7],
            matches[2],
            new Range(
                parseInt(matches[3]),
                parseInt(matches[4]),
                parseInt(matches[5]),
                parseInt(matches[6])),
            this.parseErrorTraceVariables()
        ));
    }

    private parseErrorTraceVariables(): VariableValue[] {
        const variables = [];
        for (let i = 1; i < this.msgBuffer.length; i++) {
            const line = this.msgBuffer[i];
            const matches = /^\/\\ (\w+) = (.+)$/g.exec(line);
            if (matches) {
                const name = matches[1];
                const valueLines = [matches[2]];
                this.readValueLines(i + 1, valueLines);
                i += valueLines.length - 1;
                const value = parseValueLines(valueLines);
                variables.push(new VariableValue(name, value));
            }
        }
        return variables;
    }

    private readValueLines(startIdx: number, lines: string[]) {
        for (let i = startIdx; i < this.msgBuffer.length; i++) {
            const line = this.msgBuffer[i];
            if (line.startsWith('/\\ ')) {
                return i;
            }
            lines.push(line.trim());
        }
    }

    private tryMatchBufferLine(regExp: RegExp): RegExpExecArray | null {
        if (this.msgBuffer.length === 0) {
            return null;
        }
        return regExp.exec(this.msgBuffer[0]);
    }

    private calcTimestamp(timeStr: string): string {
        if (!this.firstStatTime) {
            return '??:??:??';
        }
        const time = parseDateTime(timeStr);
        const durMsec = time.diff(this.firstStatTime);
        const dur = moment.duration(durMsec);
        const sec = leftPadTimeUnit(dur.seconds());
        const min = leftPadTimeUnit(dur.minutes());
        const hour = leftPadTimeUnit(Math.floor(dur.asHours())); // days are converted to hours
        return `${hour}:${min}:${sec}`;
    }
}

function parseIntWithComma(str: string): number {
    const c = str.split(',').join('');
    return parseInt(c);
}

function leftPadTimeUnit(n: number): string {
    return n < 10 ? '0' + n : String(n);
}
