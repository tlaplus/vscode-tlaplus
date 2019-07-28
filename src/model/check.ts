import { Range } from 'vscode';
import { DCollection } from '../diagnostic';
import { isNumber } from 'util';
import { Moment } from 'moment';

export enum CheckState {
    Running = 'R',
    Success = 'S',
    Error = 'E'
}

export enum CheckStatus {
    NotStarted,
    Starting,
    SanyParsing,
    SanyFinished,
    InitialStatesComputing,
    Checkpointing,
    CheckingLiveness,
    CheckingLivenessFinal,
    ServerRunning,
    WorkersRegistered,
    Finished
}

const STATUS_NAMES = new Map<CheckStatus, string>();
STATUS_NAMES.set(CheckStatus.NotStarted, 'Not started');
STATUS_NAMES.set(CheckStatus.Starting, 'Starting');
STATUS_NAMES.set(CheckStatus.SanyParsing, 'SANY parsing');
STATUS_NAMES.set(CheckStatus.SanyFinished, 'SANY finished');
STATUS_NAMES.set(CheckStatus.InitialStatesComputing, 'Computing initial states');
STATUS_NAMES.set(CheckStatus.Checkpointing, 'Checkpointing');
STATUS_NAMES.set(CheckStatus.CheckingLiveness, 'Checking liveness');
STATUS_NAMES.set(CheckStatus.CheckingLivenessFinal, 'Checking final liveness');
STATUS_NAMES.set(CheckStatus.ServerRunning, 'Master waiting for workers');
STATUS_NAMES.set(CheckStatus.WorkersRegistered, 'Workers connected');
STATUS_NAMES.set(CheckStatus.Finished, 'Finished');

const STATE_NAMES = new Map<CheckState, string>();
STATE_NAMES.set(CheckState.Running, '');
STATE_NAMES.set(CheckState.Success, 'successfully');
STATE_NAMES.set(CheckState.Error, 'with errors');

/**
 * Statistics on initial state generation.
 */
export class InitialStateStatItem {
    readonly timeStamp: string;
    readonly diameter: number;
    readonly total: number;
    readonly distinct: number;
    readonly queueSize: number;

    constructor(timeStamp: string, diameter: number, total: number, distinct: number, queueSize: number) {
        this.timeStamp = timeStamp;
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
 * Represents a variable value in a particular model state.
 */
export class VariableValue {
    readonly name: string;
    readonly value: Value;

    constructor(name: string, value: Value) {
        this.name = name;
        this.value = value;
    }
}

/**
 * Base class for values.
 */
export abstract class Value {
    readonly abstract str: string;

    toString() {
        return this.str;
    }
}

/**
 * Value of a primitive type: 17, "foo", TRUE, etc.
 */
export class PrimitiveValue extends Value {
    readonly str: string;

    constructor(value: string) {
        super();
        this.str = value;
    }
}

/**
 * Value that is a collection of other values.
 */
abstract class CollectionValue extends Value {
    readonly items: Value[];
    readonly str: string;

    constructor(items: Value[], prefix: string, postfix: string) {
        super();
        this.items = items;
        // TODO: trim to fit into 100 symbols
        const valuesStr = this.items.map(i => i.toString()).join(', ');
        this.str = prefix + valuesStr + postfix;
    }
}

/**
 * Represents a set: {1, "b", <<TRUE, 5>>}, {}, etc.
 */
export class SetValue extends CollectionValue {
    constructor(values: Value[]) {
        super(values, '{', '}');
    }
}

/**
 * Represents a sequence/tuple: <<1, "b", TRUE>>, <<>>, etc.
 */
export class SequenceValue extends CollectionValue {
    constructor(values: Value[]) {
        super(values, '<<', '>>');
    }
}

/**
 * An item of a structure.
 */
export class StructureItem implements Value {
    readonly key: string;
    readonly value: Value;
    readonly str: string;

    constructor(key: string, value: Value) {
        this.key = key;
        this.value = value;
        this.str = key + ' |-> ' + value;
    }

    toString() {
        return `${this.key} |-> ${this.value}`;
    }
}

/**
 * Represents a structure: [a |-> 'A', b |-> 34, c |-> <<TRUE, 2>>], [], etc.
 */
export class StructureValue extends CollectionValue {
    constructor(values: StructureItem[]) {
        super(values, '[', ']');
    }
}

/**
 * A state of a process in a particular moment of time.
 */
export class ErrorTraceItem {
    readonly num: number;
    readonly title: string;
    readonly module: string;
    readonly action: string;
    readonly range: Range;
    readonly variables: ReadonlyArray<VariableValue>;

    constructor(num: number, title: string, module: string, action: string, range: Range, variables: VariableValue[]) {
        this.num = num;
        this.title = title;
        this.module = module;
        this.action = action;
        this.range = range;
        this.variables = variables;
    }
}

/**
 * Represents the state of a TLA model checking process.
 */
export class ModelCheckResult {
    static readonly EMPTY = new ModelCheckResult(
        '', false, CheckStatus.Starting, null, [], [], [], [],
        undefined, undefined, undefined, undefined, 0, undefined);

    readonly modelName: string;
    readonly state: CheckState;
    readonly stateName: string;
    readonly success: boolean;
    readonly status: CheckStatus;
    readonly statusName: string;
    readonly processInfo: string | null;
    readonly initialStatesStat: ReadonlyArray<InitialStateStatItem>;
    readonly coverageStat: ReadonlyArray<CoverageItem>;
    readonly errors: ReadonlyArray<ReadonlyArray<string>>;
    readonly errorTrace: ReadonlyArray<ErrorTraceItem>;
    readonly sanyMessages: DCollection | undefined;
    readonly startDateTimeStr: string | undefined;
    readonly endDateTimeStr: string | undefined;
    readonly durationStr: string | undefined;
    readonly workersCount: number;
    readonly fingerprintCollisionProbability: string | undefined;

    constructor(
        modelName: string,
        success: boolean,
        status: CheckStatus,
        processInfo: string | null,
        initialStatesStat: InitialStateStatItem[],
        coverageStat: CoverageItem[],
        errors: string[][],
        errorTrace: ErrorTraceItem[],
        sanyMessages: DCollection | undefined,
        startDateTime: Moment | undefined,
        endDateTime: Moment | undefined,
        duration: number | undefined,
        workersCount: number,
        fingerprintCollisionProbability: string | undefined
    ) {
        this.modelName = modelName;
        if (status === CheckStatus.Finished) {
            this.state = success ? CheckState.Success : CheckState.Error;
        } else {
            this.state = CheckState.Running;
        }
        this.stateName = getStateName(this.state);
        this.success = success;
        this.status = status;
        this.statusName = getStatusName(status);
        this.processInfo = processInfo;
        this.initialStatesStat = initialStatesStat;
        this.coverageStat = coverageStat;
        this.errors = errors;
        this.errorTrace = errorTrace;
        this.sanyMessages = sanyMessages;
        this.startDateTimeStr = dateTimeToStr(startDateTime);
        this.endDateTimeStr = dateTimeToStr(endDateTime);
        this.durationStr = durationToStr(duration);
        this.workersCount = workersCount;
        this.fingerprintCollisionProbability = fingerprintCollisionProbability;
    }
}

function getStateName(state: CheckState): string {
    const name = STATE_NAMES.get(state);
    if (typeof name !== 'undefined') {
        return name;
    }
    throw new Error(`Name not defined for check state ${state}`);
}

export function getStatusName(status: CheckStatus): string {
    const name = STATUS_NAMES.get(status);
    if (name) {
        return name;
    }
    throw new Error(`Name not defined for check status ${status}`);
}

function dateTimeToStr(dateTime: Moment | undefined): string {
    if (!dateTime) {
        return 'not yet';
    }
    return dateTime.format('HH:mm:ss (MMM D)');
}

function durationToStr(dur: number | undefined): string {
    if (!isNumber(dur)) {
        return '';
    }
    return dur + ' msec';
}
