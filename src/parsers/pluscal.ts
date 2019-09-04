import * as vscode from 'vscode';
import { ProcessOutputHandler } from '../outputHandler';
import { Readable } from 'stream';
import { DCollection } from '../diagnostic';

class LocationInfo {
    constructor(
        readonly location: vscode.Position,
        readonly strLength: number
    ) {}
}

const ZERO_LOCATION_INFO = new LocationInfo(new vscode.Position(0, 0), 0);

/**
 * Parses stdout of PlusCal transpiler.
 */
export class TranspilerStdoutParser extends ProcessOutputHandler<DCollection> {
    private readonly filePath: string;
    private errMessage: string | null = null;

    constructor(source: Readable | string[], filePath: string) {
        super(source, new DCollection());
        this.result.addFilePath(filePath);
        this.filePath = filePath;
    }

    protected handleLine(line: string | null) {
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
            if (this.tryParseUnrecoverableError(line)) {
                return;
            }
        }
        if (this.errMessage) {
            const locInfo = this.parseLocation(line) || ZERO_LOCATION_INFO;
            this.addError(locInfo.location, this.errMessage);
            this.errMessage = null;
        }
    }

    private tryParseUnrecoverableError(line: string): boolean {
        const matchers = /^\s+--\s+(.+)$/g.exec(line);
        if (!matchers) {
            return false;
        }
        const message = matchers[1];
        if (message.startsWith('Beginning of algorithm string --algorithm not found')) {
            // This error means that there's no PlusCal code in file. Just ignore it.
            return true;
        }
        const locInfo = this.parseLocation(line);
        if (locInfo) {
            this.addError(locInfo.location, message.substring(0, message.length - locInfo.strLength));
            this.errMessage = null;
        } else {
            this.errMessage = message;
        }
        return true;
    }

    private addError(location: vscode.Position, message: string) {
        const locRange = new vscode.Range(location, location);
        this.result.addMessage(this.filePath, locRange, message);
    }

    private parseLocation(line: string): LocationInfo | undefined {
        const rxLocation = /\s*(?:at )?line (\d+), column (\d+).?\s*$/g;
        const matches = rxLocation.exec(line);
        if (!matches) {
            return undefined;
        }
        const posLine = parseInt(matches[1]) - 1;
        const posCol = parseInt(matches[2]);
        return new LocationInfo(new vscode.Position(posLine, posCol), matches[0].length);
    }
}
