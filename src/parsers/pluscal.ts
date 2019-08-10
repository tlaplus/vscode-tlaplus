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
        if (!this.errMessage && line.startsWith(' -- ')) {
            const msg = line.substring(4);
            if (msg.startsWith('Beginning of algorithm string --algorithm not found')) {
                // This error means that there's no PlusCal code in file. Just ignore it.
                return;
            }
            this.errMessage = msg;
            return;
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
}
