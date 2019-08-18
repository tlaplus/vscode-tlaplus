import { Range } from 'vscode';
import { ProcessOutputParser } from './base';
import { Readable } from 'stream';
import { CheckStatus, ModelCheckResult, InitialStateStatItem, CoverageItem, ErrorTraceItem,
    CheckState, OutputLine, StructureValue, findChanges} from '../model/check';
import { parseVariableValue } from './tlcValues';
import { SanyData, SanyStdoutParser } from './sany';
import { DCollection, addDiagnostics } from '../diagnostic';
import { parseDateTime } from '../common';
import * as moment from 'moment/moment';
import { clearTimeout } from 'timers';

const STATUS_EMIT_TIMEOUT = 500;    // msec

// TLC message types
// Declared in https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/tlc2/output/EC.java
const NONE = -1;
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
const TLC_INITIAL_STATE = 2102;
const TLC_NESTED_EXPRESSION = 2103;

const TLC_INVARIANT_VIOLATED_INITIAL = 2107;
const TLC_PROPERTY_VIOLATED_INITIAL = 2108;
const TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT = 2109;
const TLC_INVARIANT_VIOLATED_BEHAVIOR = 2110;
const TLC_INVARIANT_EVALUATION_FAILED = 2111;
const TLC_INVARIANT_VIOLATED_LEVEL = 2146;
const TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR = 2112;
const TLC_ACTION_PROPERTY_EVALUATION_FAILED = 2113;
const TLC_DEADLOCK_REACHED = 2114;

const TLC_STATES_AND_NO_NEXT_ACTION = 2115;
const TLC_TEMPORAL_PROPERTY_VIOLATED = 2116;
const TLC_FAILED_TO_RECOVER_NEXT = 2117;
const TLC_NO_STATES_SATISFYING_INIT = 2118;
const TLC_STRING_MODULE_NOT_FOUND = 2119;

const TLC_AAAAAAA = 2130;
const TLC_REGISTRY_INIT_ERROR = 2131;
const TLC_CHOOSE_ARGUMENTS_WRONG = 2164;
const TLC_CHOOSE_UPPER_BOUND = 2165;

const TLC_VALUE_ASSERT_FAILED = 2132;
const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE = 2154;
const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED = 2168;
const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH = 2400;
const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MODULE_MISMATCH = 2402;
const TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_IDENTIFIER_MISMATCH = 2403;

const TLC_STATE_PRINT1 = 2216;
const TLC_STATE_PRINT2 = 2217;
const TLC_STATE_PRINT3 = 2218;

// Config file errors
const TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM = 2222;
const TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID = 2223;
const TLC_CONFIG_WRONG_SUBSTITUTION = 2224;
const TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS = 2225;
const TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR = 2280;
const TLC_CONFIG_SUBSTITUTION_NON_CONSTANT = 2281;
const TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC = 2226;
const TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT = 2227;
const TLC_CONFIG_ID_REQUIRES_NO_ARG = 2228;
const TLC_CONFIG_SPECIFIED_NOT_DEFINED = 2229;
const TLC_CONFIG_ID_HAS_VALUE = 2230;
const TLC_CONFIG_MISSING_INIT = 2231;
const TLC_CONFIG_MISSING_NEXT = 2232;
const TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT = 2233;
const TLC_CONFIG_OP_NO_ARGS = 2234;
const TLC_CONFIG_OP_NOT_IN_SPEC = 2235;
const TLC_CONFIG_OP_IS_EQUAL = 2236;
const TLC_CONFIG_SPEC_IS_TRIVIAL = 2237;
const TLC_CANT_HANDLE_SUBSCRIPT = 2238;
const TLC_CANT_HANDLE_CONJUNCT = 2239;
const TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS = 2240;
const TLC_CONFIG_PROPERTY_NOT_CORRECTLY_DEFINED = 2241;
const TLC_CONFIG_OP_ARITY_INCONSISTENT = 2242;
const TLC_CONFIG_NO_STATE_TYPE = 2243;
const TLC_CANT_HANDLE_REAL_NUMBERS = 2244;
const TLC_NO_MODULES = 2245;

const CFG_ERROR_READING_FILE = 5001;
const CFG_GENERAL = 5002;
const CFG_MISSING_ID = 5003;
const CFG_TWICE_KEYWORD = 5004;
const CFG_EXPECT_ID = 5005;
const CFG_EXPECTED_SYMBOL = 5006;

const TLC_FINISHED = 2186;
const TLC_SUCCESS = 2193;

/**
 * Parses stdout of TLC model checker.
 */
export class TlcModelCheckerStdoutParser extends ProcessOutputParser<DCollection> {
    checkResultBuilder: ModelCheckResultBuilder;
    timer: NodeJS.Timer | undefined = undefined;
    first: boolean = true;

    constructor(
        stdout: Readable | string[],
        tlaFilePath: string | undefined,
        outFilePath: string,
        private handler: (checkResult: ModelCheckResult) => void
    ) {
        super(stdout, new DCollection());
        this.handler = handler;
        this.checkResultBuilder = new ModelCheckResultBuilder(outFilePath);
        if (tlaFilePath) {
            this.result.addFilePath(tlaFilePath);
        }
    }

    protected parseLine(line: string | null) {
        if (line !== null) {
            this.checkResultBuilder.addLine(line);
            this.scheduleUpdate();
        } else {
            this.checkResultBuilder.handleStop();
            // Copy SANY messages
            const dCol = this.checkResultBuilder.getSanyMessages();
            if (dCol) {
                addDiagnostics(dCol, this.result);
            }
            // Issue the last update
            this.issueUpdate();
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
            me.issueUpdate();
        }, timeout);
    }

    private issueUpdate() {
        if (this.timer) {
            clearTimeout(this.timer);
        }
        this.handler(this.checkResultBuilder.build());
        this.timer = undefined;
    }
}

class LineParsingResult {
    constructor(
        readonly success: boolean,
        readonly remainingLine: string
    ) {}
}

/**
 * TLC output message;
 */
class Message {
    readonly lines: string[] = [];

    constructor(readonly type: number) {}
}

/**
 * Tracks hierarchy of TLC output messages.
 */
class MessageStack {
    private static NO_MESSAGE = new Message(NONE);

    private current: Message = MessageStack.NO_MESSAGE;
    private previous: Message[] = [];

    public getCurrentType(): number {
        return this.current.type;
    }

    public start(type: number) {
        if (type === NONE) {
            throw Error('Cannot start message of type NONE');
        }
        if (this.current.type !== NONE) {
            this.previous.push(this.current);
        }
        this.current = new Message(type);
    }

    public finish(): Message {
        if (this.current.type === NONE) {
            console.error('Unexpected message end');
            return MessageStack.NO_MESSAGE;
        }
        const finished = this.current;
        this.current = this.previous.pop() || MessageStack.NO_MESSAGE;
        return finished;
    }

    public addLine(line: string) {
        if (this.current.type === NONE) {
            console.error("Unexpected line when there's no current message");
            return;
        }
        this.current.lines.push(line);
    }
}

/**
 * Gradually builds ModelCheckResult by processing TLC output lines.
 */
class ModelCheckResultBuilder {
    private state: CheckState = CheckState.Running;
    private status: CheckStatus = CheckStatus.NotStarted;
    private startDateTime: moment.Moment | undefined;
    private endDateTime: moment.Moment | undefined;
    private duration: number | undefined;       // msec
    private processInfo: string | undefined;
    private initialStatesStat: InitialStateStatItem[] = [];
    private coverageStat: CoverageItem[] = [];
    private errors: string[][] = [];
    private errorTrace: ErrorTraceItem[] = [];
    private messages = new MessageStack();
    private sanyLines: string[] = [];
    private sanyData: SanyData | undefined;
    private outputLines: OutputLine[] = [];
    private workersCount: number = 0;
    private firstStatTime: moment.Moment | undefined;
    private fingerprintCollisionProbability: string | undefined;

    constructor(private outFilePath: string) {
    }

    getStatus(): CheckStatus {
        return this.status;
    }

    getSanyMessages(): DCollection | undefined {
        return this.sanyData ? this.sanyData.dCollection : undefined;
    }

    addLine(line: string) {
        const endRes = this.tryParseMessageEnd(line);
        let eLine = line;
        if (endRes.success) {
            const message = this.messages.finish();
            this.handleMessageEnd(message);
            eLine = endRes.remainingLine;
        }
        const newMsgType = this.tryParseMessageStart(eLine);
        if (newMsgType) {
            this.messages.start(newMsgType);
            return;
        }
        if (eLine === '') {
            return;
        }
        if (this.status === CheckStatus.SanyParsing) {
            this.sanyLines.push(eLine);
            return;
        }
        if (this.messages.getCurrentType() !== NONE) {
            this.messages.addLine(eLine);
            return;
        }
        this.addOutputLine(eLine);
    }

    handleStop() {
        if (this.status !== CheckStatus.Finished) {
            // The process wasn't finished as expected, hence it was stopped manually
            this.state = CheckState.Stopped;
        }
    }

    build(): ModelCheckResult {
        return new ModelCheckResult(
            this.outFilePath,
            this.state,
            this.status,
            this.processInfo,
            this.initialStatesStat,
            this.coverageStat,
            this.errors,
            this.errorTrace,
            this.sanyData ? this.sanyData.dCollection : undefined,
            this.startDateTime,
            this.endDateTime,
            this.duration,
            this.workersCount,
            this.fingerprintCollisionProbability,
            this.outputLines
        );
    }

    private handleMessageEnd(message: Message) {
        if (this.status === CheckStatus.NotStarted) {
            this.status = CheckStatus.Starting;
        }
        switch (message.type) {
            case TLC_MODE_MC:
                this.processInfo = message.lines.join('');
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
                this.parseStarting(message.lines);
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
                this.parseInitialStatesComputed(message.lines);
                break;
            case TLC_CHECKING_TEMPORAL_PROPS:
                if (message.lines.length > 0 && message.lines[0].indexOf('complete') >= 0) {
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
                this.parseProgressStats(message.lines);
                break;
            case TLC_COVERAGE_INIT:
                this.coverageStat.length = 0;
                this.parseCoverage(message.lines);
                break;
            case TLC_COVERAGE_NEXT:
                this.parseCoverage(message.lines);
                break;
            case GENERAL:
            case TLC_INITIAL_STATE:
            case TLC_NESTED_EXPRESSION:
            case TLC_VALUE_ASSERT_FAILED:
            case TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE:
            case TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED:
            case TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH:
            case TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MODULE_MISMATCH:
            case TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_IDENTIFIER_MISMATCH:
            case TLC_INVARIANT_VIOLATED_INITIAL:
            case TLC_PROPERTY_VIOLATED_INITIAL:
            case TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT:
            case TLC_INVARIANT_VIOLATED_BEHAVIOR:
            case TLC_INVARIANT_EVALUATION_FAILED:
            case TLC_INVARIANT_VIOLATED_LEVEL:
            case TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR:
            case TLC_ACTION_PROPERTY_EVALUATION_FAILED:
            case TLC_DEADLOCK_REACHED:
            // --
            case TLC_STATES_AND_NO_NEXT_ACTION:
            case TLC_TEMPORAL_PROPERTY_VIOLATED:
            case TLC_FAILED_TO_RECOVER_NEXT:
            case TLC_NO_STATES_SATISFYING_INIT:
            case TLC_STRING_MODULE_NOT_FOUND:
            // --
            case TLC_AAAAAAA:
            case TLC_REGISTRY_INIT_ERROR:
            case TLC_CHOOSE_ARGUMENTS_WRONG:
            case TLC_CHOOSE_UPPER_BOUND:
            // --
            case TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM:
            case TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID:
            case TLC_CONFIG_WRONG_SUBSTITUTION:
            case TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS:
            case TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR:
            case TLC_CONFIG_SUBSTITUTION_NON_CONSTANT:
            case TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC:
            case TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT:
            case TLC_CONFIG_ID_REQUIRES_NO_ARG:
            case TLC_CONFIG_SPECIFIED_NOT_DEFINED:
            case TLC_CONFIG_ID_HAS_VALUE:
            case TLC_CONFIG_MISSING_INIT:
            case TLC_CONFIG_MISSING_NEXT:
            case TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT:
            case TLC_CONFIG_OP_NO_ARGS:
            case TLC_CONFIG_OP_NOT_IN_SPEC:
            case TLC_CONFIG_OP_IS_EQUAL:
            case TLC_CONFIG_SPEC_IS_TRIVIAL:
            case TLC_CANT_HANDLE_SUBSCRIPT:
            case TLC_CANT_HANDLE_CONJUNCT:
            case TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS:
            case TLC_CONFIG_PROPERTY_NOT_CORRECTLY_DEFINED:
            case TLC_CONFIG_OP_ARITY_INCONSISTENT:
            case TLC_CONFIG_NO_STATE_TYPE:
            case TLC_CANT_HANDLE_REAL_NUMBERS:
            case TLC_NO_MODULES:
            // --
            case CFG_ERROR_READING_FILE:
            case CFG_GENERAL:
            case CFG_MISSING_ID:
            case CFG_TWICE_KEYWORD:
            case CFG_EXPECT_ID:
            case CFG_EXPECTED_SYMBOL:
                this.parseErrorMessage(message.lines);
                break;
            case TLC_STATE_PRINT1:
            case TLC_STATE_PRINT2:
            case TLC_STATE_PRINT3:
                this.parseErrorTraceItem(message.lines);
                break;
            case TLC_SUCCESS:
                this.parseSuccess(message.lines);
                this.state = CheckState.Success;
                break;
            case TLC_FINISHED:
                this.status = CheckStatus.Finished;
                this.parseFinished(message.lines);
                if (this.state !== CheckState.Success) {
                    this.state = CheckState.Error;
                }
                break;
        }
    }

    private tryParseMessageStart(line: string): number | undefined {
        const matches = /^(.*)@!@!@STARTMSG (\d+)(:\d+)? @!@!@$/g.exec(line);
        if (!matches) {
            return undefined;
        }
        if (matches[1] !== '') {
            this.messages.addLine(matches[1]);
        }
        return parseInt(matches[2]);
    }

    private tryParseMessageEnd(line: string): LineParsingResult {
        const matches = /^(.*)@!@!@ENDMSG \d+ @!@!@(.*)$/g.exec(line);
        if (!matches) {
            return new LineParsingResult(false, line);
        }
        if (matches[1] !== '') {
            this.messages.addLine(matches[1]);
        }
        return new LineParsingResult(true, matches[2]);
    }

    private parseStarting(lines: string[]) {
        const matches = this.tryMatchBufferLine(lines, /^Starting\.\.\. \((\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\)$/g);
        if (matches) {
            this.startDateTime = parseDateTime(matches[1]);
        }
    }

    private parseSuccess(lines: string[]) {
        const matches = this.tryMatchBufferLine(lines, /calculated \(optimistic\):\s+val = (.+)$/g, 3);
        if (matches) {
            this.fingerprintCollisionProbability = matches[1];
        }
    }

    private parseFinished(lines: string[]) {
        const matches = this.tryMatchBufferLine(lines, /^Finished in (\d+)ms at \((\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\)$/g);
        if (matches) {
            this.duration = parseInt(matches[1]);
            this.endDateTime = parseDateTime(matches[2]);
        }
    }

    private parseSanyOutput() {
        const sany = new SanyStdoutParser(this.sanyLines);
        this.sanyData = sany.readAllSync();
        // Display SANY error messages as model checking errors
        this.sanyData.dCollection.getMessages().forEach(diag => this.errors.push([diag.diagnostic.message]));
    }

    private parseInitialStatesComputed(lines: string[]) {
        const matches = this.tryMatchBufferLine(lines, /^Finished computing initial states: (\d+) distinct state(s)? generated at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}).*$/g);
        if (matches) {
            const count = parseInt(matches[1]);
            this.firstStatTime = parseDateTime(matches[3]);
            this.initialStatesStat.push(new InitialStateStatItem('00:00:00', 0, count, count, count));
        }
    }

    private parseProgressStats(lines: string[]) {
        const matches = this.tryMatchBufferLine(lines, /^Progress\(([\d,]+)\) at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}): ([\d,]+) states generated.*, ([\d,]+) distinct states found.*, ([\d,]+) states left on queue.*/g);
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

    private parseCoverage(lines: string[]) {
        const matches = this.tryMatchBufferLine(lines, /^<(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>: (\d+):(\d+)/g);
        if (matches) {
            const moduleName = matches[6];
            const actionName = matches[1];
            this.coverageStat.push(new CoverageItem(
                moduleName,
                actionName,
                this.getModulePath(moduleName),
                new Range(
                    parseInt(matches[2]) - 1,
                    parseInt(matches[3]) - 1,
                    parseInt(matches[4]) - 1,
                    parseInt(matches[5])
                ),
                parseInt(matches[7]),
                parseInt(matches[8])
            ));
        }
    }

    private parseErrorMessage(lines: string[]) {
        if (lines.length === 0) {
            return;
        }
        if (lines[0] === 'TLC threw an unexpected exception.' && this.errors.length > 0) {
            // Such message must be combined with the previous one (that was actually nested)
            const prevError = this.errors[this.errors.length - 1];
            this.errors[this.errors.length - 1] = lines.concat(prevError);
        } else {
            this.errors.push(lines);
        }
    }

    private parseErrorTraceItem(lines: string[]) {
        if (lines.length === 0) {
            console.log('Error trace expected but message buffer is empty');
            return;
        }
        let traceItem;
        // Try special cases like <Initial predicate>, <Stuttering>, etc.
        const sMatches = this.tryMatchBufferLine(lines, /^(\d+): <([\w\s]+)>$/g);
        if (sMatches) {
            const itemVars = this.parseErrorTraceVariables(lines);
            traceItem = new ErrorTraceItem(
                parseInt(sMatches[1]),
                sMatches[2],
                '', '', undefined, new Range(0, 0, 0, 0), itemVars);
        } else {
            // Otherwise fall back to simple states
            const matches = this.tryMatchBufferLine(lines, /^(\d+): <(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>$/g);
            if (!matches) {
                return;
            }
            const itemVars = this.parseErrorTraceVariables(lines);
            const actionName = matches[2];
            const moduleName = matches[7];
            traceItem = new ErrorTraceItem(
                parseInt(matches[1]),
                `${actionName} in ${moduleName}`,
                moduleName,
                actionName,
                this.getModulePath(moduleName),
                new Range(
                    parseInt(matches[3]) - 1,
                    parseInt(matches[4]) - 1,
                    parseInt(matches[5]) - 1,
                    parseInt(matches[6])),
                itemVars
            );
        }
        if (this.errorTrace.length > 0) {
            findChanges(this.errorTrace[this.errorTrace.length - 1].variables, traceItem.variables);
        }
        this.errorTrace.push(traceItem);
    }

    private parseErrorTraceVariables(lines: string[]): StructureValue {
        const variables = [];
        for (let i = 1; i < lines.length; i++) {
            const line = lines[i];
            const matches = /^(?:\/\\ )?(\w+) = (.+)$/g.exec(line);
            if (matches) {
                const name = matches[1];
                const valueLines = [matches[2]];
                this.readValueLines(i + 1, lines, valueLines);
                i += valueLines.length - 1;
                const value = parseVariableValue(name, valueLines);
                variables.push(value);
            }
        }
        return new StructureValue('', variables);
    }

    private readValueLines(startIdx: number, lines: string[], valueLines: string[]) {
        for (let i = startIdx; i < lines.length; i++) {
            const line = lines[i];
            if (line.startsWith('/\\ ')) {
                return;
            }
            valueLines.push(line.trim());
        }
    }

    private tryMatchBufferLine(lines: string[], regExp: RegExp, n?: number): RegExpExecArray | null {
        const en = n ? n : 0;
        if (lines.length < en + 1) {
            return null;
        }
        return regExp.exec(lines[en]);
    }

    private calcTimestamp(timeStr: string): string {
        if (!this.firstStatTime) {
            return '00:00:00';
        }
        const time = parseDateTime(timeStr);
        const durMsec = time.diff(this.firstStatTime);
        const dur = moment.duration(durMsec);
        const sec = leftPadTimeUnit(dur.seconds());
        const min = leftPadTimeUnit(dur.minutes());
        const hour = leftPadTimeUnit(Math.floor(dur.asHours())); // days are converted to hours
        return `${hour}:${min}:${sec}`;
    }

    private addOutputLine(line: string) {
        const prevLine = this.outputLines.length > 0 ? this.outputLines[this.outputLines.length - 1] : undefined;
        if (prevLine && prevLine.text === line) {
            prevLine.increment();
        } else {
            this.outputLines.push(new OutputLine(line));
        }
    }

    private getModulePath(moduleName: string): string | undefined {
        return this.sanyData ? this.sanyData.modulePaths.get(moduleName) : undefined;
    }
}

function parseIntWithComma(str: string): number {
    const c = str.split(',').join('');
    return parseInt(c);
}

function leftPadTimeUnit(n: number): string {
    return n < 10 ? '0' + n : String(n);
}
