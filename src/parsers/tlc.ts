import { Range, Position, window } from 'vscode';
import * as moment from 'moment/moment';
import { Readable } from 'stream';
import { clearTimeout } from 'timers';
import { CheckStatus, ModelCheckResult, InitialStateStatItem, CoverageItem, MessageLine, MessageSpan, ErrorTraceItem,
    CheckState, OutputLine, StructureValue, findChanges, ModelCheckResultSource, WarningInfo,
    ErrorInfo,
    SpecFiles} from '../model/check';
import { ProcessOutputHandler } from '../outputHandler';
import { parseVariableValue } from './tlcValues';
import { SanyData, SanyStdoutParser } from './sany';
import { DCollection, addDiagnostics } from '../diagnostic';
import { parseDateTime } from '../common';
import * as msg from './tlcCodes';
import { getTlcCode, TlcCodeType } from './tlcCodes';

const STATUS_EMIT_TIMEOUT = 500;    // msec

// TLC message severity from
// https://github.com/tlaplus/tlaplus/blob/2f229f1d3e5ed1e2eadeff3bcd877b416e45d477/tlatools/src/tlc2/output/MP.java
const SEVERITY_ERROR = 1;
const SEVERITY_TLC_BUG = 2;
const SEVERITY_WARNING = 3;

/**
 * Parses stdout of TLC model checker.
 */
export class TlcModelCheckerStdoutParser extends ProcessOutputHandler<DCollection> {
    checkResultBuilder: ModelCheckResultBuilder;
    timer: NodeJS.Timer | undefined = undefined;
    first = true;

    constructor(
        source: ModelCheckResultSource,
        stdout: Readable | string[],
        specFiles: SpecFiles | undefined,
        showFullOutput: boolean,
        private handler: (checkResult: ModelCheckResult) => void
    ) {
        super(stdout, new DCollection());
        this.handler = handler;
        this.checkResultBuilder = new ModelCheckResultBuilder(source, specFiles, showFullOutput);
        if (specFiles) {
            this.result.addFilePath(specFiles.tlaFilePath);
        }
    }

    protected handleLine(line: string | null): void {
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
        this.timer = setTimeout(() => {
            this.issueUpdate();
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
 * Represents a message type, parsed from its header.
 * 1000   -> { 1000, undefined }
 * 1000:1 -> { 1000, Error }
 * 3044:3 -> { 3044, Warning }
 * etc.
 */
class MessageType {
    static readonly Unknown = new MessageType(-1938477103983);      // Some constant that is not used as a TLC code

    constructor(
        readonly code: number,
        readonly forcedType?: TlcCodeType
    ) {}

    isUnknown(): boolean {
        return this.code === MessageType.Unknown.code;
    }
}

/**
 * TLC output message.
 */
class Message {
    readonly lines: string[] = [];

    constructor(readonly type: MessageType) {}
}

/**
 * Tracks hierarchy of TLC output messages.
 */
class MessageStack {
    private static NO_MESSAGE = new Message(MessageType.Unknown);

    private current: Message = MessageStack.NO_MESSAGE;
    private previous: Message[] = [];

    public getCurrentType(): MessageType {
        return this.current.type;
    }

    public start(type: MessageType) {
        if (type.isUnknown()) {
            throw Error('Cannot start message of unknown type');
        }
        this.previous.push(this.current);
        this.current = new Message(type);
    }

    public finish(): Message {
        if (this.current.type.isUnknown()) {
            window.showErrorMessage('Unexpected message end');
            console.error('Unexpected message end');
            return MessageStack.NO_MESSAGE;
        }
        const finished = this.current;
        this.current = this.previous.pop() || MessageStack.NO_MESSAGE;
        return finished;
    }

    public addLine(line: string) {
        if (this.current.type.isUnknown()) {
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
    private warnings: WarningInfo[] = [];
    private errors: ErrorInfo[] = [];
    private messages = new MessageStack();
    private sanyLines: string[] = [];
    private sanyData: SanyData | undefined;
    private outputLines: OutputLine[] = [];
    private workersCount = 0;
    private firstStatTime: moment.Moment | undefined;
    private fingerprintCollisionProbability: string | undefined;

    constructor(
        private source: ModelCheckResultSource,
        private specFiles: SpecFiles | undefined,
        private showFullOutput: boolean
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
        if (!this.messages.getCurrentType().isUnknown()) {
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
            this.specFiles,
            this.showFullOutput,
            this.state,
            this.status,
            this.processInfo,
            this.initialStatesStat,
            this.coverageStat,
            this.warnings,
            this.errors,
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
        const tlcCode = getTlcCode(message.type.code);
        if (!tlcCode) {
            window.showErrorMessage(`Unexpected message code: ${message.type.code}`);
            return;
        }
        if (tlcCode.type === TlcCodeType.Ignore) {
            // Ignoring has precedence over forced type, otherwise there will bee to much noise
            // in the Error section
            return;
        }
        const effectiveType = message.type.forcedType ? message.type.forcedType : tlcCode.type;
        if (effectiveType === TlcCodeType.Warning) {
            this.parseWarningMessage(message.lines);
            return;
        }
        if (effectiveType === TlcCodeType.Error) {
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
            case msg.GENERAL:
            case msg.TLC_MODULE_OVERRIDE_STDOUT:
                message.lines.forEach((line) => this.addOutputLine(line));
                break;
            case msg.TLC_SUCCESS:
                this.parseSuccess(message.lines);
                this.state = this.errors.length === 0
                    ? CheckState.Success
                    : CheckState.Error;     // There might be error messages if the -continue option was used
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

    private tryParseMessageStart(line: string): MessageType | undefined {
        const matches = /^(.*)@!@!@STARTMSG (-?\d+)(:\d+)? @!@!@$/g.exec(line);
        if (!matches) {
            return undefined;
        }
        if (matches[1] !== '') {
            this.messages.addLine(matches[1]);
        }
        const code = parseInt(matches[2]);
        let forcedType;
        if (matches[3] !== '') {
            const severity = parseInt(matches[3].substring(1));
            if (severity === SEVERITY_ERROR || severity === SEVERITY_TLC_BUG) {
                forcedType = TlcCodeType.Error;
            } else if (severity === SEVERITY_WARNING) {
                forcedType = TlcCodeType.Warning;
            }
        }
        return new MessageType(code, forcedType);
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
        const regex = /^Finished in (\d+)ms at \((\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\)$/g;
        const matches = this.tryMatchBufferLine(lines, regex);
        if (matches) {
            this.duration = parseInt(matches[1]);
            this.endDateTime = parseDateTime(matches[2]);
        }
    }

    private parseSanyOutput() {
        const sany = new SanyStdoutParser(this.sanyLines);
        this.sanyData = sany.readAllSync();
        // Display SANY error messages as model checking errors
        this.sanyData.dCollection.getMessages().forEach(diag => {
            const errMessage = MessageLine.fromText(diag.diagnostic.message);
            this.errors.push(new ErrorInfo([errMessage], []));
        });
    }

    private parseInitialStatesComputed(lines: string[]) {
        // eslint-disable-next-line max-len
        const regex = /^Finished computing initial states: (\d+) distinct state(s)? generated at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}).*$/g;
        const matches = this.tryMatchBufferLine(lines, regex);
        if (matches) {
            const count = parseInt(matches[1]);
            this.firstStatTime = parseDateTime(matches[3]);
            this.initialStatesStat.push(new InitialStateStatItem('00:00:00', 0, count, count, count));
        }
    }

    private parseProgressStats(lines: string[]) {
        // eslint-disable-next-line max-len
        const regex = /^Progress\(([\d,]+)\) at (\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}): ([\d,]+) states generated.*, ([\d,]+) distinct states found.*, ([\d,]+) states left on queue.*/g;
        const matches = this.tryMatchBufferLine(lines, regex);
        if (matches) {
            const item = new InitialStateStatItem(
                this.calcTimestamp(matches[2]),
                parseIntWithComma(matches[1]),
                parseIntWithComma(matches[3]),
                parseIntWithComma(matches[4]),
                parseIntWithComma(matches[5])
            );
            if (this.initialStatesStat.length > 0
                && this.initialStatesStat[this.initialStatesStat.length - 1].timeStamp === item.timeStamp) {
                this.initialStatesStat[this.initialStatesStat.length - 1] = item;
            } else {
                this.initialStatesStat.push(item);
            }
        }
    }

    private parseCoverage(lines: string[]) {
        const regex = /^<(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>: (\d+):(\d+)/g;
        const matches = this.tryMatchBufferLine(lines, regex);
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
        const msgLines = lines.map((l) => this.makeMessageLine(l));
        this.warnings.push(new WarningInfo(msgLines));
    }

    private parseErrorMessage(lines: string[]) {
        if (lines.length === 0) {
            return;
        }
        const msgLines = lines.map((l) => this.makeMessageLine(l));
        if (lines[0] === 'TLC threw an unexpected exception.' && this.errors.length > 0) {
            // Such message must be combined with the previous one (that was actually nested)
            const prevError = this.errors[this.errors.length - 1];
            prevError.lines = msgLines.concat(prevError.lines);
            return;
        }
        this.errors.push(new ErrorInfo(msgLines, []));
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
        if (this.errors.length === 0) {
            this.errors.push(new ErrorInfo([this.makeMessageLine('[Unknown error]')], []));
        }
        const lastError = this.errors[this.errors.length - 1];
        if (checkChanges) {
            findChanges(lastError.errorTrace[lastError.errorTrace.length - 1].variables, traceItem.variables);
        }
        lastError.errorTrace.push(traceItem);
    }

    private tryParseSimpleErrorTraceItem(lines: string[]): ErrorTraceItem | undefined {
        const regex = /^(\d+): <(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>$/g;
        const matches = this.tryMatchBufferLine(lines, regex);
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
        const regex = /^(\d+): Back to state: <(\w+) line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)>?/g;
        const matches = this.tryMatchBufferLine(lines, regex);
        if (!matches) {
            return undefined;
        }
        const itemVars = this.parseErrorTraceVariables(lines);
        const actionName = matches[2];
        const moduleName = matches[7];
        const num = parseInt(matches[1]) + 1;   // looks like a shift-by-one error in the Toolbox
        return new ErrorTraceItem(
            num,
            'Back to state',
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

    private makeMessageLine(line: string): MessageLine {
        const matches = /^(.*)\b((?:L|l)ine (\d+), column (\d+) to line \d+, column \d+ in (\w+))\b(.*)$/g.exec(line);
        const modulePath = matches ? this.getModulePath(matches[5]) : undefined;
        if (!matches || !modulePath) {
            return MessageLine.fromText(line);
        }
        const spans = [];
        if (matches[1] !== '') {
            spans.push(MessageSpan.newTextSpan(matches[1]));
        }
        spans.push(MessageSpan.newSourceLinkSpan(
            matches[2],
            modulePath,
            new Position(parseInt(matches[3]) - 1, parseInt(matches[4]) - 1)
        ));
        if (matches[6] !== '') {
            spans.push(MessageSpan.newTextSpan(matches[6]));
        }
        return new MessageLine(spans);
    }
}

function parseIntWithComma(str: string): number {
    const c = str.split(',').join('');
    return parseInt(c);
}

function leftPadTimeUnit(n: number): string {
    return n < 10 ? '0' + n : String(n);
}
