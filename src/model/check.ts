import { Range } from 'vscode';
import { DCollection } from '../diagnostic';
import { isNumber } from 'util';
import { Moment } from 'moment';

export enum CheckState {
    Running = 'R',
    Success = 'S',
    Error = 'E',
    Stopped = 'X'
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
STATE_NAMES.set(CheckState.Running, 'Running');
STATE_NAMES.set(CheckState.Success, 'Success');
STATE_NAMES.set(CheckState.Error, 'Errors');
STATE_NAMES.set(CheckState.Stopped, 'Stopped');

/**
 * Statistics on initial state generation.
 */
export class InitialStateStatItem {
    constructor(
        readonly timeStamp: string,
        readonly diameter: number,
        readonly total: number,
        readonly distinct: number,
        readonly queueSize: number
    ) {}
}

/**
 * Statistics on coverage.
 */
export class CoverageItem {
    constructor(
        readonly module: string,
        readonly action: string,
        readonly location: Range,
        readonly total: number,
        readonly distinct: number
    ) {}
}

export type ValueKey = string | number;

/**
 * Base class for values.
 */
export class Value {
    constructor(
        readonly key: ValueKey,
        readonly str: string
    ) {}
}

/**
 * Value that is a collection of other values.
 */
abstract class CollectionValue extends Value {
    constructor(key: ValueKey, readonly items: Value[], prefix: string, postfix: string, toStr?: (v: Value) => string) {
        super(key, makeCollectionValueString(items, prefix, postfix, toStr || CollectionValue.valueToString));
    }

    static valueToString(v: Value) {
        return v.str;
    }
}

/**
 * Represents a set: {1, "b", <<TRUE, 5>>}, {}, etc.
 */
export class SetValue extends CollectionValue {
    constructor(key: ValueKey, items: Value[]) {
        super(key, items, '{', '}');
    }
}

/**
 * Represents a sequence/tuple: <<1, "b", TRUE>>, <<>>, etc.
 */
export class SequenceValue extends CollectionValue {
    constructor(key: ValueKey, items: Value[]) {
        super(key, items, '<<', '>>');
    }
}

/**
 * Represents a structure: [a |-> 'A', b |-> 34, c |-> <<TRUE, 2>>], [], etc.
 */
export class StructureValue extends CollectionValue {
    constructor(key: ValueKey, items: Value[]) {
        super(key, items.sort(StructureValue.compareItems), '[', ']', StructureValue.itemToString);
    }

    static itemToString(item: Value) {
        return `${item.key} |-> ${item.str}`;
    }

    static compareItems(a: Value, b: Value): number {
        if (a.key < b.key) {
            return -1;
        } else if (a.key > b.key) {
            return 1;
        }
        return 0;
    }
}

/**
 * A state of a process in a particular moment of time.
 */
export class ErrorTraceItem {
    constructor(
        readonly num: number,
        readonly title: string,
        readonly module: string,
        readonly action: string,
        readonly range: Range,
        readonly variables: StructureValue  // Variables are presented as items of a structure
    ) {}
}

/**
 * An output line produced by Print/PrintT along with the number of consecutive occurrences.
 */
export class OutputLine {
    count: number = 1;

    constructor(readonly text: string) {
    }

    increment() {
        this.count += 1;
    }
}

/**
 * Represents the state of a TLA model checking process.
 */
export class ModelCheckResult {
    static readonly EMPTY = new ModelCheckResult(
        '', CheckState.Running, CheckStatus.Starting, undefined, [], [], [], [],
        undefined, undefined, undefined, undefined, 0, undefined, []);

    readonly stateName: string;
    readonly startDateTimeStr: string | undefined;
    readonly endDateTimeStr: string | undefined;
    readonly durationStr: string | undefined;
    readonly statusDetails: string | undefined;

    constructor(
        readonly modelName: string,
        readonly state: CheckState,
        readonly status: CheckStatus,
        readonly processInfo: string | undefined,
        readonly initialStatesStat: InitialStateStatItem[],
        readonly coverageStat: CoverageItem[],
        readonly errors: string[][],
        readonly errorTrace: ErrorTraceItem[],
        readonly sanyMessages: DCollection | undefined,
        readonly startDateTime: Moment | undefined,
        readonly endDateTime: Moment | undefined,
        readonly duration: number | undefined,
        readonly workersCount: number,
        readonly collisionProbability: string | undefined,
        readonly outputLines: OutputLine[]
    ) {
        this.stateName = getStateName(this.state);
        this.startDateTimeStr = dateTimeToStr(startDateTime);
        this.endDateTimeStr = dateTimeToStr(endDateTime);
        this.durationStr = durationToStr(duration);
        let statusDetails;
        switch (state) {
            case CheckState.Running:
                statusDetails = getStatusName(status);
                break;
            case CheckState.Success:
                statusDetails = collisionProbability
                    ? `Fingerprint collission probability: ${collisionProbability}`
                    : '';
                break;
            case CheckState.Error:
                statusDetails = `${errors.length} error(s)`;
                break;
        }
        this.statusDetails = statusDetails;
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

function makeCollectionValueString(items: Value[], prefix: string, postfix: string, toStr: (v: Value) => string) {
    // TODO: trim to fit into 100 symbols
    const valuesStr = items.map(i => toStr(i)).join(', ');
    return prefix + valuesStr + postfix;
}
