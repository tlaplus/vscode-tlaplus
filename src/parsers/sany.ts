import * as vscode from 'vscode';
import { Readable } from 'stream';
import { ProcessOutputHandler } from '../outputHandler';
import { DCollection } from '../diagnostic';
import { pathToModuleName } from '../common';
import { readFileSync } from 'fs';

enum OutBlockType {
    Parsing,
    Errors,
    ParseError,
    AbortMessages,
    Warnings,
    StackTrace
}

export class SanyData {
    readonly dCollection = new DCollection();
    readonly modulePaths = new Map<string, string>();
    readonly filePathToMonolithFilePath = new Map<string, string>();
}

/**
 * Parses stdout of TLA+ code parser.
 */
export class SanyStdoutParser extends ProcessOutputHandler<SanyData> {
    rootModulePath: string | undefined;
    monolithFilePath: string | undefined;
    curFilePath: string | undefined;
    outBlockType = OutBlockType.Parsing;
    errRange: vscode.Range | undefined;
    errMessage: string | undefined;
    pendingAbortMessage = false;

    constructor(source: Readable | string[] | null) {
        super(source, new SanyData());
    }

    protected handleLine(line: string | null): void {
        if (line === null) {
            this.tryAddMessage(true);           // Add error message when there's no range
            return;
        }
        if (line === '') {
            return;
        }
        if (line.startsWith('Parsing file ')) {
            const modPath = line.substring(13);
            this.rememberParsedModule(modPath);
            return;
        }
        if (line.startsWith('Semantic processing of module ')) {
            const curMod = line.substring(30);
            this.curFilePath = this.result.modulePaths.get(curMod);
            return;
        }
        let newBlockType;
        let newErrMessage;
        if (line.startsWith('*** Errors:')) {
            newBlockType = OutBlockType.Errors;
        } else if (line.startsWith('***Parse Error***')) {
            newBlockType = OutBlockType.ParseError;
        } else if (line.startsWith('*** Abort messages:')) {
            newBlockType = OutBlockType.AbortMessages;
        } else if (line.startsWith('*** Warnings:')) {
            newBlockType = OutBlockType.Warnings;
        } else if (line.startsWith('Fatal errors while parsing TLA+ spec')) {
            this.tryAddMonolithSpec(line);
            newBlockType = OutBlockType.ParseError;
            newErrMessage = line.trim();
        } else if (line.startsWith('Residual stack trace follows:')) {
            newBlockType = OutBlockType.StackTrace;
        }
        if (newBlockType) {
            if (this.outBlockType !== OutBlockType.StackTrace) {
                this.tryAddMessage(true);
            }
            this.resetErrData();
            this.outBlockType = newBlockType;
            this.errMessage = newErrMessage;
            return;
        }
        this.tryParseOutLine(line);
    }

    private tryAddMonolithSpec(line: string) {
        const curMod = line.substring(45).split('\.')[0];
        const actualFilePath = this.result.modulePaths.get(curMod);
        const sanyData = this.result;
        // If current file path differs from the actual file path, it means we are in a monolith spec.
        // Monolith specs are TLA files which have multiple modules inline.
        if (this.curFilePath && actualFilePath && actualFilePath !== this.curFilePath) {
            const filePath = this.curFilePath;
            const monolithFilePath = actualFilePath;
            // Adapt monolith error locations.
            // It modifies the Sany result adding the module offset for in the monolith spec.  
            const invertedModulePaths = new Map(Array.from(sanyData.modulePaths, (i) => i.reverse() as [string, string]));
            const text = readFileSync(monolithFilePath).toString();
            const specName = invertedModulePaths.get(filePath);
            text.split('\n').forEach(function (line, number) {
                if (new RegExp(`-----*\\s*MODULE\\s+${specName}\\s*----*`).exec(line)) {
                    sanyData.dCollection.getMessages().filter(m => m.filePath === filePath).forEach(message => {
                        const oldRange = message.diagnostic.range;
                        // Remove message so it does not appear duplicated in the output.
                        sanyData.dCollection.removeMessage(message);
                        sanyData.dCollection.addMessage(
                            monolithFilePath, 
                            new vscode.Range(oldRange.start.line + number, oldRange.start.character, oldRange.end.line + number, oldRange.end.character),
                            message.diagnostic.message,
                            message.diagnostic.severity);
                    })
                } 
            });
        }
    }

    private tryParseOutLine(line: string) {
        if (line === 'SANY finished.') {
            return;
        }
        let range: vscode.Range | undefined;
        switch (this.outBlockType) {
            case OutBlockType.Parsing:
                this.tryParseLexicalError(line);
                break;
            case OutBlockType.Errors:
            case OutBlockType.Warnings:
                range = this.tryParseErrorRange(line);
                if (range) {
                    if (this.errRange) {
                        this.tryAddMessage();   // We found the beginning of a new message, so finish the previous one
                    }
                    this.errRange = range;
                } else {
                    this.appendErrMessage(line);
                }
                return;
            case OutBlockType.ParseError:
                this.appendErrMessage(line);
                this.tryParseParseErrorRange(line);
                break;
            case OutBlockType.AbortMessages:
                this.tryParseAbortError(line);
                break;
        }
        this.tryAddMessage();
    }

    private resetErrData() {
        this.errRange = undefined;
        this.errMessage = undefined;
        this.pendingAbortMessage = false;
    }

    private tryAddMessage(ignoreNoRange = false) {
        if (this.outBlockType === OutBlockType.StackTrace) {
            return;
        }
        if (!this.errRange && this.errMessage?.endsWith('sany.semantic.AbortException')) {
            // This message only means that there're other parsing errors
            this.resetErrData();
            return;
        }
        if (this.curFilePath && this.errMessage && (this.errRange || ignoreNoRange)) {
            const severity = this.outBlockType === OutBlockType.Warnings
                ? vscode.DiagnosticSeverity.Warning
                : vscode.DiagnosticSeverity.Error;
            const range = this.errRange || new vscode.Range(0, 0, 0, 0);
            this.result.dCollection.addMessage(this.curFilePath, range, this.errMessage, severity);
            this.resetErrData();
        }
    }

    private rememberParsedModule(modulePath: string) {
        const modName = pathToModuleName(modulePath);
        this.result.modulePaths.set(modName, modulePath);
        this.result.dCollection.addFilePath(modulePath);
        this.curFilePath = modulePath;
        if (!this.rootModulePath) {
            this.rootModulePath = modulePath;
        }
    }

    private tryParseLexicalError(line: string) {
        const rxError = /^\s*Lexical error at line (\d+), column (\d+).\s*(.*)$/g;
        const errMatches = rxError.exec(line);
        if (!errMatches) {
            return;
        }
        const errLine = parseInt(errMatches[1]) - 1;
        const errCol = parseInt(errMatches[2]) - 1;
        this.errMessage = errMatches[3];
        this.errRange = new vscode.Range(errLine, errCol, errLine, errCol);
    }

    private tryParseErrorRange(line: string): vscode.Range | undefined {
        const rxPosition = /^\s*line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)\s*$/g;
        const posMatches = rxPosition.exec(line);
        if (!posMatches) {
            return undefined;
        }
        return new vscode.Range(
            parseInt(posMatches[1]) - 1,
            parseInt(posMatches[2]) - 1,
            parseInt(posMatches[3]) - 1,
            parseInt(posMatches[4])
        );
    }

    private tryParseParseErrorRange(line: string) {
        const rxPosition = /\bat line (\d+), col(?:umn)? (\d+)\s+.*$/g;
        const posMatches = rxPosition.exec(line);
        if (!posMatches) {
            return;
        }
        const errLine = parseInt(posMatches[1]) - 1;
        const errCol = parseInt(posMatches[2]) - 1;
        this.errRange = new vscode.Range(errLine, errCol, errLine, errCol);
    }

    // Parses abort messages with unknown locations
    private tryParseAbortError(line: string) {
        if (line === 'Unknown location') {
            this.pendingAbortMessage = true;
            return;
        }
        if (!this.pendingAbortMessage || !this.rootModulePath) {
            return;
        }
        if (line.startsWith('Circular dependency')) {
            // Have to wait for the next line that will contain the recursion description
            this.errMessage = line;
            return;
        }
        const message = this.errMessage ? this.errMessage + '\n' + line : line;
        this.result.dCollection.addMessage(this.rootModulePath, new vscode.Range(0, 0, 0, 0), message);
        this.resetErrData();
    }

    private appendErrMessage(line: string) {
        if (!this.errMessage) {
            this.errMessage = line.trim();
        } else {
            this.errMessage += '\n' + line.trim();
        }
    }
}
