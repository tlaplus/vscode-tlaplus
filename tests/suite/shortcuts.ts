import * as vscode from 'vscode';
import moment = require('moment');
import { Moment } from 'moment';
import { Value, ValueKey, SetValue, SequenceValue, StructureValue, SimpleFunction,
    InitialStateStatItem, CoverageItem, ModelCheckResult, CheckState, CheckStatus,
    ErrorTraceItem, OutputLine } from '../../src/model/check';
import { DCollection } from '../../src/diagnostic';

export function v(key: ValueKey, value: string): Value {
    return new Value(key, value);
}

export function set(key: ValueKey, ...items: Value[]): SetValue {
    return new SetValue(key, items);
}

export function seq(key: ValueKey, ...items: Value[]): SequenceValue {
    return new SequenceValue(key, items);
}

export function struct(key: ValueKey, ...items: Value[]): StructureValue {
    return new StructureValue(key, items);
}

export function func(key: ValueKey, from: Value, to: Value): SimpleFunction {
    return new SimpleFunction(key, from, to);
}

export function range(fromLine: number, fromChar: number, toLine: number, toChar: number): vscode.Range {
    return new vscode.Range(new vscode.Position(fromLine, fromChar), new vscode.Position(toLine, toChar));
}

export class CheckResultBuilder {
    private processInfo: string | undefined;
    private initialStatesStat: InitialStateStatItem[] = [];
    private coverageStat: CoverageItem[] = [];
    private errors: string[][] = [];
    private errorTrace: ErrorTraceItem[] = [];
    private sanyMessages: DCollection | undefined;
    private startDateTime: Moment | undefined;
    private endDateTime: Moment | undefined;
    private duration: number | undefined;
    private workersCount: number = 0;
    private collisionProbability: string | undefined;
    private outputLines: OutputLine[] = [];

    constructor(
        readonly outFilePath: string,
        readonly checkState: CheckState,
        readonly checkStatus: CheckStatus
    ) {}

    build(): ModelCheckResult {
        return new ModelCheckResult(
            this.outFilePath,
            this.checkState,
            this.checkStatus,
            this.processInfo,
            this.initialStatesStat,
            this.coverageStat,
            this.errors,
            this.errorTrace,
            this.sanyMessages,
            this.startDateTime,
            this.endDateTime,
            this.duration,
            this.workersCount,
            this.collisionProbability,
            this.outputLines
        );
    }

    setProcessInfo(pi: string): CheckResultBuilder {
        this.processInfo = pi;
        return this;
    }

    setStartDateTime(start: string): CheckResultBuilder {
        this.startDateTime = moment(start);
        return this;
    }

    setDuration(dur: number): CheckResultBuilder {
        this.duration = dur;
        return this;
    }

    setEndDateTime(end: string): CheckResultBuilder {
        this.endDateTime = moment(end);
        return this;
    }

    setWorkersCount(wc: number): CheckResultBuilder {
        this.workersCount = wc;
        return this;
    }

    addInitState(
        timeStamp: string, diameter: number, total: number, distinct: number, queueSize: number
    ): CheckResultBuilder {
        this.initialStatesStat.push(new InitialStateStatItem(timeStamp, diameter, total, distinct, queueSize));
        return this;
    }

    addCoverage(
        module: string,
        action: string,
        filePath: string | undefined,
        range: vscode.Range,
        total: number,
        distinct: number
    ): CheckResultBuilder {
        this.coverageStat.push(new CoverageItem(module, action, filePath, range, total, distinct));
        return this;
    }

    addOutLine(text: string, count?: number): CheckResultBuilder {
        const line = new OutputLine(text);
        if (count && count > 1) {
            for (let i = 0; i < count - 1; i++) {
                line.increment();
            }
        }
        this.outputLines.push(line);
        return this;
    }

    addError(lines: string[]): CheckResultBuilder {
        this.errors.push(lines);
        return this;
    }

    addDColFilePath(path: string): CheckResultBuilder {
        this.ensureSanyMessages();
        this.sanyMessages!.addFilePath(path);
        return this;
    }

    addDColMessage(filePath: string, range: vscode.Range, text: string): CheckResultBuilder {
        this.ensureSanyMessages();
        this.sanyMessages!.addMessage(filePath, range, text);
        return this;
    }

    addTraceItem(
        title: string,
        module: string,
        action: string,
        filePath: string | undefined,
        range: vscode.Range,
        variables: StructureValue  // Variables are presented as items of a structure
    ): CheckResultBuilder {
        const num = this.errorTrace.length + 1;
        this.errorTrace.push(new ErrorTraceItem(num, title, module, action, filePath, range, variables));
        return this;
    }

    private ensureSanyMessages() {
        if (!this.sanyMessages) {
            this.sanyMessages = new DCollection();
        }
    }
}
