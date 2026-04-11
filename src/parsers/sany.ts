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

export type DivergenceType = 'none' | 'pcal' | 'tla' | 'both';

export type DivergenceResult = Map<string, DivergenceType>;

const DIVERGENCE_PRIORITY: Record<DivergenceType, number> = {
    'none': 0, 'pcal': 1, 'tla': 2, 'both': 3
};

/**
 * Determines the type of PlusCal/TLA+ divergence from SANY output.
 *
 * Returns a map from module name to divergence type for each
 * divergent module.  An empty map means no divergence was detected.
 */
export function getDivergenceType(sanyData: SanyData): DivergenceResult {
    const warnings = sanyData.dCollection.getMessages().filter(
        msg => msg.diagnostic.severity === vscode.DiagnosticSeverity.Warning
    );
    const modules = new Map<string, DivergenceType>();
    for (const w of warnings) {
        const msg = w.diagnostic.message;
        let dtype: DivergenceType | undefined;
        if (msg.includes('have changed since the last translation')) {
            dtype = 'both';
        } else if (msg.includes('TLA+ translation')) {
            dtype = 'tla';
        } else if (msg.includes('PlusCal algorithm') && msg.includes('has changed since')) {
            dtype = 'pcal';
        }
        if (dtype) {
            const modName = pathToModuleName(w.filePath);
            const existing = modules.get(modName);
            if (!existing || DIVERGENCE_PRIORITY[dtype] > DIVERGENCE_PRIORITY[existing]) {
                modules.set(modName, dtype);
            }
        }
    }
    return modules;
}

const TRANSLATION_CHECKSUM_RE = /^\\[*] BEGIN TRANSLATION\s*\(/m;

/**
 * Quick check whether a document contains a BEGIN TRANSLATION marker with checksums.
 * Only files with checksums can have detectable divergence.
 */
export function hasTranslationChecksums(text: string): boolean {
    return TRANSLATION_CHECKSUM_RE.test(text);
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
    public getFileContents =
        (filePath : string) : string => readFileSync(filePath).toString(); // this should be set only at tests

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
            this.tryParseModulePath(line.substring(13));
            return;
        }
        if (line.startsWith('Semantic processing of module ')) {
            // Flush any pending rangeless message (e.g. divergence warning from syntax parsing phase)
            // before switching to a new module context
            this.tryAddMessage(true);
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
        } else if (line.startsWith('*** Warnings:') || line.startsWith('Warnings (')) {
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
        const curMod = line.substring(45).split('.')[0];
        const actualFilePath = this.result.modulePaths.get(curMod);
        const sanyData = this.result;
        // If current file path differs from the actual file path, it means we are in a monolith spec.
        // Monolith specs are TLA files which have multiple modules inline.
        if (this.curFilePath && actualFilePath && actualFilePath !== this.curFilePath) {
            const filePath = this.curFilePath;
            const monolithFilePath = actualFilePath;
            // Adapt monolith error locations.
            // It modifies the Sany result adding the module offset in the monolith spec.
            const invertedModulePaths = new Map(
                Array.from(sanyData.modulePaths, (i) => i.reverse() as [string, string])
            );
            const text = this.getFileContents(monolithFilePath);
            const specName = invertedModulePaths.get(filePath);
            const moduleHeaderRegex = new RegExp(`^\\s*-{4,}\\s*(MODULE)\\s*${specName}\\s*-{4,}`);
            text.split('\n').every(function(line, number) {
                if (moduleHeaderRegex.test(line)) {
                    sanyData.dCollection.getMessages().filter(m => m.filePath === filePath).forEach(message => {
                        const oldRange = message.diagnostic.range;
                        // Remove message so it does not appear duplicated in the output.
                        sanyData.dCollection.removeMessage(message);
                        sanyData.dCollection.addMessage(
                            monolithFilePath,
                            new vscode.Range(
                                oldRange.start.line + number,
                                oldRange.start.character,
                                oldRange.end.line + number,
                                oldRange.end.character),
                            message.diagnostic.message,
                            message.diagnostic.severity);
                    });
                    return false; // Break out from `every`.
                }
                return true;
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
                    } else if (this.errMessage) {
                        // Flush a rangeless message (e.g. PlusCal divergence warning) before starting a ranged one
                        this.tryAddMessage(true);
                    }
                    this.errRange = range;
                } else if (this.tryParseModuleSwitch(line)) {
                    // tryParseModuleSwitch flushes the pending message internally
                    // before switching curFilePath, then starts the new message.
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

    private tryParseModulePath(line: string) {
        const rxModulePath = /^(.*)(?: \(.*\))$/g;
        const moldulePathMatches = rxModulePath.exec(line);
        const modulePath = moldulePathMatches ? moldulePathMatches[1] : line;
        this.rememberParsedModule(modulePath);
    }

    /**
     * Detects "In module X" lines inside Warnings/Errors blocks.
     * When a different module is named, switches curFilePath so subsequent
     * messages are attributed to the correct file.  Returns true if the
     * line matched the pattern.
     */
    private tryParseModuleSwitch(line: string): boolean {
        const match = /^In module (\w+)$/.exec(line);
        if (!match) {
            return false;
        }
        const modName = match[1];
        const modPath = this.result.modulePaths.get(modName);
        if (modPath) {
            this.tryAddMessage(true);
            this.curFilePath = modPath;
        }
        this.appendErrMessage(line);
        return true;
    }

    private appendErrMessage(line: string) {
        if (!this.errMessage) {
            this.errMessage = line.trim();
        } else {
            this.errMessage += '\n' + line.trim();
        }
    }
}
