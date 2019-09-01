import * as vscode from 'vscode';
import { ProcessOutputParser } from './base';
import { Readable } from 'stream';
import { DCollection } from '../diagnostic';

/**
 * Parses stdout of PlusCal transpiler.
 */
export class TranspilerStdoutParser extends ProcessOutputParser<DCollection> {
    private readonly filePath: string;
    private errMessage: string | null = null;

    constructor(source: Readable | string[], filePath: string) {
        super(source, new DCollection());
        this.result.addFilePath(filePath);
        this.filePath = filePath;
    }

    protected parseLine(line: string | null) {
        if (line === null) {
            if (this.errMessage !== null) {
                this.result.addMessage(this.filePath, new vscode.Range(0, 0, 0, 0), this.errMessage);
            }
            return;
        }
        if (line === '') {
            return;
        }
        if (!this.errMessage) {
            if (this.tryUnrecoverableError(line)) {
                return;
            }
        }
        if (this.errMessage) {
            const rxPosition = /^\s+(?:at )?line (\d+), column (\d+).?\s*$/g;
            const posMatches = rxPosition.exec(line);
            if (posMatches) {
                const posLine = parseInt(posMatches[1]) - 1;
                const posCol = parseInt(posMatches[2]);
                this.result.addMessage(
                    this.filePath!,
                    new vscode.Range(posLine, posCol, posLine, posCol),
                    this.errMessage);
            }
            this.errMessage = null;
            return;
        }
    }

    private tryUnrecoverableError(line: string): boolean {
        const matchers = /^\s+--\s+(.+)$/g.exec(line);
        if (!matchers) {
            return false;
        }
        const message = matchers[1];
        if (message.startsWith('Beginning of algorithm string --algorithm not found')) {
            // This error means that there's no PlusCal code in file. Just ignore it.
            return true;
        }
        const posMatcher = /\s*(?:at )?line (\d+), column (\d+).?\s*$/g.exec(line);
        if (posMatcher) {
            const posLine = parseInt(posMatcher[1]) - 1;
            const posCol = parseInt(posMatcher[2]);
            this.result.addMessage(
                this.filePath!,
                new vscode.Range(posLine, posCol, posLine, posCol),
                message.substring(0, message.length - posMatcher[0].length));
            this.errMessage = null;
        } else {
            this.errMessage = message;
        }
        return true;
    }
}
