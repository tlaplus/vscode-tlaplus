import * as vscode from 'vscode';
import moment = require('moment');
import { Moment } from 'moment';
import { Value, ValueKey, SetValue, SequenceValue, StructureValue, SimpleFunction,
    InitialStateStatItem, CoverageItem, ModelCheckResult, CheckState, CheckStatus, MessageLine, MessageSpan,
    ErrorTraceItem, OutputLine, ModelCheckResultSource, SimpleFunctionItem, ErrorInfo,
    WarningInfo } from '../../src/model/check';
import { DCollection } from '../../src/diagnostic';
import { ROOT_CONTAINER_NAME } from '../../src/symbols/tlaSymbols';

type MessageSpanSrc = string | MessageSpan;

export function v(key: ValueKey, value: string): Value {
    return new Value(key, value);
}

export function n(key: ValueKey, name: string): Value {
    return new Value(key, name);
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

export function funcItem(key: ValueKey, from: Value, to: Value): SimpleFunctionItem {
    return new SimpleFunctionItem(key, from, to);
}

export function func(key: ValueKey, from: Value, to: Value): SimpleFunction {
    return new SimpleFunction(key, [ funcItem(1, from, to) ]);
}

export function funcMerge(key: ValueKey, ...items: SimpleFunctionItem[]): SimpleFunction {
    return new SimpleFunction(key, items);
}

export function pos(line: number, char: number): vscode.Position {
    return new vscode.Position(line, char);
}

export function range(fromLine: number, fromChar: number, toLine: number, toChar: number): vscode.Range {
    return new vscode.Range(pos(fromLine, fromChar), pos(toLine, toChar));
}

export function loc(docUri: vscode.Uri, rangeOrPos: vscode.Range | vscode.Position): vscode.Location {
    return new vscode.Location(docUri, rangeOrPos);
}

export function message(...spans: MessageSpanSrc[]): MessageLine {
    const eSpans = spans.map((s) => {
        return s instanceof MessageSpan ? s : MessageSpan.newTextSpan(s);
    });
    return new MessageLine(eSpans);
}

export function sourceLink(text: string, filePath: string, locaction: vscode.Position): MessageSpan {
    return MessageSpan.newSourceLinkSpan(text, filePath, locaction);
}

export function symModule(name: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(name, vscode.SymbolKind.Module, ROOT_CONTAINER_NAME, location);
}

export function symPlusCal(name: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(
        name,
        vscode.SymbolKind.Namespace,
        ROOT_CONTAINER_NAME,
        location
    );
}

export function symFunc(name: string, parentName: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(name, vscode.SymbolKind.Function, parentName, location);
}

export function symField(name: string, parentName: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(name, vscode.SymbolKind.Field, parentName, location);
}

export function symConst(name: string, parentName: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(name, vscode.SymbolKind.Constant, parentName, location);
}

export function symVar(name: string, parentName: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(name, vscode.SymbolKind.Variable, parentName, location);
}

export function symModRef(name: string, parentName: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(name, vscode.SymbolKind.Namespace, parentName, location);
}

export function symBool(name: string, parentName: string, location: vscode.Location): vscode.SymbolInformation {
    return new vscode.SymbolInformation(name, vscode.SymbolKind.Boolean, parentName, location);
}

export function traceItem(
    num: number,
    title: string,
    module: string,
    action: string,
    filePath: string | undefined,
    range: vscode.Range,
    variables: StructureValue  // Variables are presented as items of a structure
): ErrorTraceItem {
    return new ErrorTraceItem(num, title, module, action, filePath, range, variables);
}

export class CheckResultBuilder {
    private processInfo: string | undefined;
    private initialStatesStat: InitialStateStatItem[] = [];
    private coverageStat: CoverageItem[] = [];
    private warnings: WarningInfo[] = [];
    private errors: ErrorInfo[] = [];
    private sanyMessages: DCollection | undefined;
    private startDateTime: Moment | undefined;
    private endDateTime: Moment | undefined;
    private duration: number | undefined;
    private workersCount = 0;
    private collisionProbability: string | undefined;
    private outputLines: OutputLine[] = [];

    constructor(
        readonly outFilePath: string,
        readonly checkState: CheckState,
        readonly checkStatus: CheckStatus
    ) {}

    build(): ModelCheckResult {
        return new ModelCheckResult(
            ModelCheckResultSource.OutFile,
            undefined,
            false,
            this.checkState,
            this.checkStatus,
            this.processInfo,
            this.initialStatesStat,
            this.coverageStat,
            this.warnings,
            this.errors,
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

    addWarning(lines: MessageLine[]): CheckResultBuilder {
        this.warnings.push(new WarningInfo(lines));
        return this;
    }

    addError(lines: MessageLine[], errorTrace: ErrorTraceItem[] = []): CheckResultBuilder {
        this.errors.push(new ErrorInfo(lines, errorTrace));
        return this;
    }

    addDColFilePath(path: string): CheckResultBuilder {
        this.ensureSanyMessages();
        this.sanyMessages?.addFilePath(path);
        return this;
    }

    addDColMessage(
        filePath: string,
        range: vscode.Range,
        text: string,
        severity: vscode.DiagnosticSeverity
    ): CheckResultBuilder {
        this.ensureSanyMessages();
        this.sanyMessages?.addMessage(filePath, range, text, severity);
        return this;
    }

    private ensureSanyMessages() {
        if (!this.sanyMessages) {
            this.sanyMessages = new DCollection();
        }
    }
}
