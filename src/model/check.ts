import { Range, Position } from 'vscode';
import * as path from 'path';
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
    SuccessorStatesComputing,
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
STATUS_NAMES.set(CheckStatus.SuccessorStatesComputing, 'Computing reachable states');
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

const VALUE_FORMAT_LENGTH_THRESHOLD = 30;

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
        readonly filePath: string | undefined,
        readonly range: Range,
        readonly total: number,
        readonly distinct: number
    ) {}
}

enum MessageSpanType {
    Text = 'T',
    SourceLink = 'SL'
}

export class MessageSpan {
    private constructor(
        readonly type: MessageSpanType,
        readonly text: string,
        readonly filePath?: string | undefined,
        readonly location?: Position | undefined
    ) {}

    static newTextSpan(text: string): MessageSpan {
        return new MessageSpan(MessageSpanType.Text, text);
    }

    static newSourceLinkSpan(text: string, filePath: string, location: Position): MessageSpan {
        return new MessageSpan(MessageSpanType.SourceLink, text, filePath, location);
    }
}

/**
 * Represents an error or warning line of a message.
 */
export class MessageLine {
    constructor(
        readonly spans: ReadonlyArray<MessageSpan>
    ) {}

    static fromText(text: string): MessageLine {
        return new MessageLine([ MessageSpan.newTextSpan(text) ]);
    }

    toString(): string {
        return this.spans.map((s) => s.text).join('');
    }
}

export type ValueKey = string | number;

/**
 * Type of value change between two consecutive states.
 */
export enum Change {
    NOT_CHANGED = 'N',
    ADDED = 'A',
    MODIFIED = 'M',
    DELETED = 'D'
}

/**
 * Base class for values.
 */
export class Value {
    static idCounter = 0;
    static idStep = 1;
    changeType = Change.NOT_CHANGED;
    readonly id: number;

    constructor(
        readonly key: ValueKey,
        readonly str: string
    ) {
        Value.idCounter += Value.idStep;
        this.id = Value.idCounter;
    }

    /**
     * Switches off ID incrementation. For tests only.
     */
    static switchIdsOff(): void {
        Value.idStep = 0;
    }

    /**
     * Switches on ID incrementation. For tests only.
     */
    static switchIdsOn(): void {
        Value.idStep = 1;
    }

    setModified(): Value {
        this.changeType = Change.MODIFIED;
        return this;
    }

    setAdded(): Value {
        this.changeType = Change.ADDED;
        return this;
    }

    setDeleted(): Value {
        this.changeType = Change.MODIFIED;
        return this;
    }

    /**
     * Adds formatted representation of the value to the given array of strings.
     */
    format(indent: string): string {
        return `${this.str}`;
    }
}

/**
 * A value that is represented by some variable name.
 */
export class NameValue extends Value {
    constructor(key: ValueKey, name: string) {
        super(key, name);
    }
}

/**
 * Value that is a collection of other values.
 */
export abstract class CollectionValue extends Value {
    readonly expandSingle = true;
    deletedItems: Value[] | undefined;

    constructor(
        key: ValueKey,
        readonly items: Value[],
        readonly prefix: string,
        readonly postfix: string,
        readonly delim = ', ',
        toStr?: (v: Value) => string
    ) {
        super(key, makeCollectionValueString(items, prefix, postfix, delim, toStr || (v => v.str)));
    }

    addDeletedItems(items: Value[]): CollectionValue {
        if (!items || items.length === 0) {
            return this;
        }
        if (!this.deletedItems) {
            this.deletedItems = [];
        }
        const delItems = this.deletedItems;
        items.forEach(delItem => {
            const newValue = new Value(delItem.key, delItem.str);   // No need in deep copy here
            newValue.changeType = Change.DELETED;
            delItems.push(newValue);
        });
        return this;
    }

    findItem(id: number): Value | undefined {
        for (const item of this.items) {
            if (item.changeType === Change.DELETED) {
                continue;
            }
            if (item.id === id) {
                return item;
            }
            if (item instanceof CollectionValue) {
                const subItem = item.findItem(id);
                if (subItem) {
                    return subItem;
                }
            }
        }
        return undefined;
    }

    format(indent: string): string {
        if (this.items.length === 0) {
            return `${this.prefix}${this.postfix}`;
        }
        if (this.str.length <= VALUE_FORMAT_LENGTH_THRESHOLD) {
            return this.str;
        }
        const subIndent = indent + '  ';
        const fmtFunc = (v: Value) => this.formatKey(subIndent, v) + '' + v.format(subIndent);
        const body = makeCollectionValueString(this.items, '', '', this.delim + '\n', fmtFunc);
        return `${this.prefix}\n${body}\n${indent}${this.postfix}`;
    }

    formatKey(indent: string, value: Value): string {
        return `${indent}${value.key}: `;
    }
}

/**
 * Represents a set: {1, "b", <<TRUE, 5>>}, {}, etc.
 */
export class SetValue extends CollectionValue {
    constructor(key: ValueKey, items: Value[]) {
        super(key, items, '{', '}');
    }

    setModified(): SetValue {
        super.setModified();
        return this;
    }

    formatKey(indent: string, _: Value): string {
        return indent;
    }

    diff(other: Value): boolean {
        if (!(other instanceof SetValue)) {
            return false;
        }

        const o = (other as SetValue);

        let modified = false;
        const deletedItems = [];

        let i = 0;
        for (; i < this.items.length; i++) {
            let notfound = true;
            let j = 0;
            while (notfound && j < o.items.length) {
                if (this.items[i].str === o.items[j].str) {
                    notfound = false;
                }
                j++;
            }
            if (notfound) {
                deletedItems.push(this.items[i]);
                modified = true;
            }
        }
        if (deletedItems.length > 0) {
            o.addDeletedItems(deletedItems);
            o.setModified();
        }

        for (i = 0; i < o.items.length; i++) {
            let notfound = true;
            let j = 0;
            while (notfound && j < this.items.length) {
                if (this.items[j].str === o.items[i].str) {
                    notfound = false;
                }
                j++;
            }
            if (notfound) {
                o.items[i].setAdded();
                o.setModified();
            }
        }
        return modified;
    }
}

/**
 * Represents a sequence/tuple: <<1, "b", TRUE>>, <<>>, etc.
 */
export class SequenceValue extends CollectionValue {
    constructor(key: ValueKey, items: Value[]) {
        super(key, items, '<<', '>>');
    }

    formatKey(indent: string, _: Value): string {
        return indent;
    }
}

/**
 * Represents a structure: [a |-> 'A', b |-> 34, c |-> <<TRUE, 2>>], [], etc.
 */
export class StructureValue extends CollectionValue {
    constructor(
        key: ValueKey,
        items: Value[],
        prefix = '[',
        postfix = ']',
        delim = ', ',
        readonly itemSep = ' |-> ',
        toStr = StructureValue.itemToString,
        preserveOrder = false) {
        super(key, items, prefix, postfix, delim, toStr);
        if (!preserveOrder) {
            items.sort(StructureValue.compareItems);
        }
    }

    static itemToString(item: Value): string {
        return `${item.key} |-> ${item.str}`;
    }

    static funcItemToString(item: Value): string {
        return `${item.key} :> ${item.str}`;
    }

    static compareItems(a: Value, b: Value): number {
        if (a.key < b.key) {
            return -1;
        } else if (a.key > b.key) {
            return 1;
        }
        return 0;
    }

    setModified(): StructureValue {
        super.setModified();
        return this;
    }

    formatKey(indent: string, value: Value): string {
        return `${indent}${value.key}` + this.itemSep;
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
        readonly filePath: string | undefined,
        readonly range: Range,
        readonly variables: StructureValue  // Variables are presented as items of a structure
    ) {}
}

/**
 * An output line produced by Print/PrintT along with the number of consecutive occurrences.
 */
export class OutputLine {
    count = 1;

    constructor(readonly text: string) {
    }

    increment(): void {
        this.count += 1;
    }
}

/**
 * A warning, issued by TLC.
 */
export class WarningInfo {
    constructor(
        readonly lines: MessageLine[]
    ) {}
}

/**
 * An error, issued by TLC.
 */
export class ErrorInfo {
    constructor(
        public lines: MessageLine[],
        readonly errorTrace: ErrorTraceItem[]
    ) {}
}

export enum ModelCheckResultSource {
    Process,    // The result comes from an ongoing TLC process
    OutFile     // The result comes from a .out file
}

export class SpecFiles {
    readonly tlaFileName: string;
    readonly cfgFileName: string;

    constructor(
        readonly tlaFilePath: string,
        readonly cfgFilePath: string
    ) {
        this.tlaFileName = path.basename(tlaFilePath);
        this.cfgFileName = path.basename(cfgFilePath);
    }
}

/**
 * Represents the state of a TLA model checking process.
 */
export class ModelCheckResult {

    readonly stateName: string;
    readonly startDateTimeStr: string | undefined;
    readonly endDateTimeStr: string | undefined;
    readonly durationStr: string | undefined;
    readonly statusDetails: string | undefined;

    constructor(
        readonly source: ModelCheckResultSource,
        readonly specFiles: SpecFiles | unknown,
        readonly showFullOutput: boolean,
        readonly state: CheckState,
        readonly status: CheckStatus,
        readonly processInfo: string | undefined,
        readonly initialStatesStat: InitialStateStatItem[],
        readonly coverageStat: CoverageItem[],
        readonly warnings: WarningInfo[],
        readonly errors: ErrorInfo[],
        readonly sanyMessages: DCollection | undefined,
        readonly startDateTime: Moment | undefined,
        readonly endDateTime: Moment | undefined,
        readonly duration: number | undefined,
        readonly workersCount: number,
        readonly collisionProbability: string | undefined,
        readonly outputLines: OutputLine[],
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
                    ? `Fingerprint collision probability: ${collisionProbability}`
                    : '';
                break;
            case CheckState.Error:
                statusDetails = `${errors.length} error(s)`;
                break;
        }
        this.statusDetails = statusDetails;
    }

    static createEmpty(source: ModelCheckResultSource): ModelCheckResult {
        return new ModelCheckResult(
            source, undefined, false, CheckState.Running, CheckStatus.Starting, undefined, [], [], [], [],
            undefined, undefined, undefined, undefined, 0, undefined, []);
    }

    formatValue(valueId: number): string | undefined {
        for (const err of this.errors) {
            for (const items of err.errorTrace) {
                const value = items.variables.findItem(valueId);
                if (value) {
                    return value.format('');
                }
            }
        }
        return undefined;
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

/**
 * Recursively finds and marks all the changes between two collections.
 */
export function findChanges(prev: CollectionValue, state: CollectionValue): boolean {
    let pi = 0;
    let si = 0;
    let modified = false;
    const deletedItems = [];
    while (pi < prev.items.length && si < state.items.length) {
        const prevValue = prev.items[pi];
        const stateValue = state.items[si];
        if (prevValue.key > stateValue.key) {
            stateValue.changeType = Change.ADDED;
            modified = true;
            si += 1;
        } else if (prevValue.key < stateValue.key) {
            deletedItems.push(prevValue);
            pi += 1;
        } else {
            if (prevValue instanceof SetValue && stateValue instanceof SetValue) {
                modified = prevValue.diff(stateValue) || modified;
            } else if (prevValue instanceof CollectionValue && stateValue instanceof CollectionValue) {
                modified = findChanges(prevValue, stateValue) || modified;
            } else if (prevValue.str !== stateValue.str) {
                stateValue.changeType = Change.MODIFIED;
                modified = true;
            }
            si += 1;
            pi += 1;
        }
    }
    for (; si < state.items.length; si++) {
        state.items[si].changeType = Change.ADDED;
        modified = true;
    }
    for (; pi < prev.items.length; pi++) {
        deletedItems.push(prev.items[pi]);
    }
    state.addDeletedItems(deletedItems);
    modified = modified || deletedItems.length > 0;
    if (modified) {
        state.changeType = Change.MODIFIED;
    }
    return modified;
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
    return `${dur} msec`;
}

function makeCollectionValueString(
    items: Value[],
    prefix: string,
    postfix: string,
    delimiter: string,
    toStr: (v: Value) => string
) {
    // TODO: trim to fit into 100 symbols
    const valuesStr = items
        .filter(i => i.changeType !== Change.DELETED)
        .map(i => toStr(i))
        .join(delimiter);
    return prefix + valuesStr + postfix;
}
