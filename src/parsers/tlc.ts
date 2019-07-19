import * as vscode from 'vscode';
import * as path from 'path';
import { ProcessOutputParser } from '../tla2tools';
import { Readable } from 'stream';

/**
 * Parses stdout of TLA+ code parser.
 */
export class TLAParserStdoutParser extends ProcessOutputParser {
    modPaths: Map<string, string> = new Map();
    curFilePath: string | undefined = undefined;
    errBlock: string = 'no';                // no, errors, parse_errors
    errRange: vscode.Range | null = null;
    errMessage: string | null = null;

    constructor(stdout: Readable) {
        super(stdout);
    }

    protected parseLine(line: string | null): void {
        console.log('lc> ' + (line === null ? ':END:' : line));
        if (line === null || line === '') {
            return;
        }
        if (line.startsWith('Parsing file ')) {
            const modPath = line.substring(13);
            const sid = modPath.lastIndexOf(path.sep);
            const modName = modPath.substring(sid + 1, modPath.length - 4);   // remove path and .tla
            this.modPaths.set(modName, modPath);
            this.addDiagnosticFilePath(modPath);
            this.curFilePath = modPath;
            return;
        }
        if (line.startsWith('Semantic processing of module ')) {
            const curMod = line.substring(30);
            this.curFilePath = this.modPaths.get(curMod);
            return;
        }
        if (line.startsWith('*** Errors:')) {
            this.errBlock = 'errors';
            this.resetErrData();
            return;
        }
        if (line.startsWith('***Parse Error***')) {
            this.errBlock = 'parse_errors';
            this.resetErrData();
            return;
        }
        if (this.errBlock === 'no') {
            const rxError = /^\s*Lexical error at line (\d+), column (\d+).\s*(.*)$/g;
            const errMatches = rxError.exec(line);
            if (errMatches) {
                const errLine = parseInt(errMatches[1]) - 1;
                const errCol = parseInt(errMatches[2]) - 1;
                this.errMessage = errMatches[3];
                this.errRange = new vscode.Range(errLine, errCol, errLine, errCol);
            }
        } else if (this.errBlock === 'errors') {
            if (this.errRange === null) {
                const rxPosition = /^\s*line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)\s*$/g;
                const posMatches = rxPosition.exec(line);
                if (posMatches) {
                    this.errRange = new vscode.Range(
                        parseInt(posMatches[1]) - 1,
                        parseInt(posMatches[2]) - 1,
                        parseInt(posMatches[3]) - 1,
                        parseInt(posMatches[4])
                    );
                }
                return;
            }
            this.errMessage = line.trim();
        } else if (this.errBlock === 'parse_errors') {
            if (this.errMessage === null) {
                this.errMessage = line.trim();
                return;
            }
            const rxPosition = /^.*\s+at line (\d+), column (\d+)\s+.*$/g;
            const posMatches = rxPosition.exec(line);
            if (posMatches) {
                const errLine = parseInt(posMatches[1]) - 1;
                const errCol = parseInt(posMatches[2]) - 1;
                this.errRange = new vscode.Range(errLine, errCol, errLine, errCol);
            }
        }
        this.tryAddMessage();
    }

    private resetErrData() {
        this.errRange = null;
        this.errMessage = null;
    }

    private tryAddMessage() {
        if (this.curFilePath && this.errMessage && this.errRange) {
            this.addDiagnosticMessage(this.curFilePath, this.errRange, this.errMessage);
            this.resetErrData();
        }
    }
}
