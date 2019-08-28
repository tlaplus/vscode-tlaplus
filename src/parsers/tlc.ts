import { Range, window } from 'vscode';
import * as moment from 'moment/moment';
import { Readable } from 'stream';
import { clearTimeout } from 'timers';
import { CheckStatus, ModelCheckResult, InitialStateStatItem, CoverageItem, ErrorTraceItem,
    CheckState, OutputLine, StructureValue, findChanges, ModelCheckResultSource} from '../model/check';
import { ProcessOutputParser } from './base';
import { parseVariableValue } from './tlcValues';
import { SanyData, SanyStdoutParser } from './sany';
import { DCollection, addDiagnostics } from '../diagnostic';
import { parseDateTime } from '../common';
import * as msg from './tlcCodes';
import { getTlcCode, TlcCodeType } from './tlcCodes';

const STATUS_EMIT_TIMEOUT = 500;    // msec
const NONE = -1938477103984;

/**
 * Parses stdout of TLC model checker.
 */
export class TlcModelCheckerStdoutParser extends ProcessOutputParser<DCollection> {
    checkResultBuilder: ModelCheckResultBuilder;
    timer: NodeJS.Timer | undefined = undefined;
    first: boolean = true;

    constructor(
        source: ModelCheckResultSource,
        stdout: Readable | string[],
        tlaFilePath: string | undefined,
        outFilePath: string,
        private handler: (checkResult: ModelCheckResult) => void
    ) {
        super(stdout, new DCollection());
        this.handler = handler;
        this.checkResultBuilder = new ModelCheckResultBuilder(source, outFilePath);
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
            window.showErrorMessage('Unexpected message end');
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
    private warnings: string[][] = [];
    private errors: string[][] = [];
    private errorTrace: ErrorTraceItem[] = [];
    private messages = new MessageStack();
    private sanyLines: string[] = [];
    private sanyData: SanyData | undefined;
    private outputLines: OutputLine[] = [];
    private workersCount: number = 0;
    private firstStatTime: moment.Moment | undefined;
    private fingerprintCollisionProbability: string | undefined;

    constructor(
        private source: ModelCheckResultSource,
        private outFilePath: string
    ) {}

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
            this.source,
            this.outFilePath,
            this.state,
            this.status,
            this.processInfo,
            this.initialStatesStat,
            this.coverageStat,
            this.warnings,
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
        const tlcCode = getTlcCode(message.type);
        if (!tlcCode) {
            window.showErrorMessage(`Unexpected message code ${message.type}`);
            return;
        }
        if (tlcCode.type === TlcCodeType.Ignore) {
            return;
        }
        if (tlcCode.type === TlcCodeType.Warning) {
            this.parseWarningMessage(message.lines);
            return;
        }
        if (tlcCode.type === TlcCodeType.Error) {
            this.parseErrorMessage(message.lines);
            return;
        }
        switch (tlcCode) {
            case msg.TLC_MODE_MC:
                this.processInfo = message.lines.join('');
                break;
            case msg.TLC_SANY_START:
                this.status = CheckStatus.SanyParsing;
                break;
            case msg.TLC_SANY_END:
                this.status = CheckStatus.SanyFinished;
                this.parseSanyOutput();
                break;
            case msg.TLC_CHECKPOINT_START:
                this.status = CheckStatus.Checkpointing;
                break;
            case msg.TLC_STARTING:
                this.parseStarting(message.lines);
                break;
            case msg.TLC_COMPUTING_INIT:
                this.status = CheckStatus.InitialStatesComputing;
                break;
            case msg.TLC_COMPUTING_INIT_PROGRESS:
                this.status = CheckStatus.InitialStatesComputing;
                break;
            case msg.TLC_INIT_GENERATED1:
            case msg.TLC_INIT_GENERATED2:
            case msg.TLC_INIT_GENERATED3:
            case msg.TLC_INIT_GENERATED4:
                this.parseInitialStatesComputed(message.lines);
                break;
            case msg.TLC_CHECKING_TEMPORAL_PROPS:
                if (message.lines.length > 0 && message.lines[0].indexOf('complete') >= 0) {
                    this.status = CheckStatus.CheckingLivenessFinal;
                } else {
                    this.status = CheckStatus.CheckingLiveness;
                }
                break;
            case msg.TLC_DISTRIBUTED_SERVER_RUNNING:
                this.status = CheckStatus.ServerRunning;
                break;
            case msg.TLC_DISTRIBUTED_WORKER_REGISTERED:
                this.status = CheckStatus.WorkersRegistered;
                this.workersCount += 1;
                break;
            case msg.TLC_DISTRIBUTED_WORKER_DEREGISTERED:
                this.workersCount -= 1;
                break;
            case msg.TLC_PROGRESS_STATS:
                this.parseProgressStats(message.lines);
                break;
            case msg.TLC_COVERAGE_INIT:
                this.coverageStat.length = 0;
                this.parseCoverage(message.lines);
                break;
            case msg.TLC_COVERAGE_NEXT:
                this.parseCoverage(message.lines);
                break;
            case msg.TLC_STATE_PRINT1:
            case msg.TLC_STATE_PRINT2:
            case msg.TLC_STATE_PRINT3:
            case msg.TLC_BACK_TO_STATE:
                this.parseErrorTraceItem(message.lines);
                break;
            case msg.TLC_SUCCESS:
                this.parseSuccess(message.lines);
                this.state = CheckState.Success;
                break;
            case msg.TLC_FINISHED:
                this.status = CheckStatus.Finished;
                this.parseFinished(message.lines);
                if (this.state !== CheckState.Success) {
                    this.state = CheckState.Error;
                }
                break;
            default:
                window.showErrorMessage(`No handler for message of type ${message.type}`);
                console.error(`No handler for message of type ${message.type}, text: ${message.lines.join('\n')}`);
        }
    }

    private tryParseMessageStart(line: string): number | undefined {
        const matches = /^(.*)@!@!@STARTMSG (-?\d+)(:\d+)? @!@!@$/g.exec(line);
        if (!matches) {
            return undefined;
        }
        if (matches[1] !== '') {
            this.messages.addLine(matches[1]);
        }
        return parseInt(matches[2]);
    }

    private tryParseMessageEnd(line: string): LineParsingResult {
        const matches = /^(.*)@!@!@ENDMSG -?\d+ @!@!@(.*)$/g.exec(line);
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
                parseInt(matches[8]),
                parseInt(matches[7])
            ));
        }
    }

    private parseWarningMessage(lines: string[]) {
        if (lines.length === 0) {
            return;
        }
        this.warnings.push(lines);
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
        let traceItem = this.tryParseSimpleErrorTraceItem(lines);
        const checkChanges = traceItem instanceof ErrorTraceItem;
        if (!traceItem) {
            traceItem = this.tryParseSpecialErrorTraceItem(lines);
        }
        if (!traceItem) {
            traceItem = this.tryParseBackToStateErrorTraceItem(lines);
        }
        if (!traceItem) {
            console.error(`Cannot parse error trace item: ${lines[0]}`);
            const itemVars = this.parseErrorTraceVariables(lines);
            traceItem = new ErrorTraceItem(
                0, lines[1], '', '', undefined, new Range(0, 0, 0, 0), itemVars
            );
        }
        if (checkChanges && this.errorTrace.length > 0) {
            findChanges(this.errorTrace[this.errorTrace.length - 1].variables, traceItem.variables);
        }
        this.errorTrace.push(traceItem);
    }

    private tryParseSimpleErrorTraceItem(lines: string[]): ErrorTraceItem | undefined {
        const matches = this.tryMatchBufferLine(lines, /^(\d+): <(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>$/g);
        if (!matches) {
            return undefined;
        }
        const itemVars = this.parseErrorTraceVariables(lines);
        const actionName = matches[2];
        const moduleName = matches[7];
        return new ErrorTraceItem(
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

    private tryParseSpecialErrorTraceItem(lines: string[]): ErrorTraceItem | undefined {
        // Try special cases like "Initial predicate", "Stuttering", etc.
        const matches = this.tryMatchBufferLine(lines, /^(\d+): <?([\w\s]+)>?$/g);
        if (!matches) {
            return undefined;
        }
        const itemVars = this.parseErrorTraceVariables(lines);
        return new ErrorTraceItem(
            parseInt(matches[1]),
            matches[2],
            '', '', undefined, new Range(0, 0, 0, 0), itemVars
        );
    }

    private tryParseBackToStateErrorTraceItem(lines: string[]): ErrorTraceItem | undefined {
        // Try special cases "Back to state: <...>"
        const matches = this.tryMatchBufferLine(lines, /^(\d+): Back to state: <(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>?/g);
        if (!matches) {
            return undefined;
        }
        const itemVars = this.parseErrorTraceVariables(lines);
        const actionName = matches[2];
        const moduleName = matches[7];
        const num = parseInt(matches[1]) + 1;   // looks like a shift-by-one error in the Toolbox
        return new ErrorTraceItem(
            num,
            `Back to state ${num}`,
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
