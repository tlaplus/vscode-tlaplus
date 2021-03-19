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

// Error message postfix as defined in PcalDebug.java in the tla toolbox. Excludes the trailing newline since we
// parse one line at a time
const ERROR_POSTFIX = '.';

/**
 * Parses stdout of PlusCal transpiler.
 */
export class TranspilerStdoutParser extends ProcessOutputHandler<DCollection> {
    private readonly filePath: string;
    private errMessage: string | null = null;
    private nextLineIsError = false;

    constructor(source: Readable | string[] | null, filePath: string) {
        super(source, new DCollection());
        this.result.addFilePath(filePath);
        this.filePath = filePath;
    }

    protected handleLine(line: string | null): void {
        if (line === null) {
            if (this.errMessage !== null) {
                this.result.addMessage(this.filePath, new vscode.Range(0, 0, 0, 0), this.errMessage);
            }
            return;
        }
        if (line === '') {
            return;
        }
        // If nextLineIsError is set, we expect the next line to contain a full error message, not just a location
        if (!this.errMessage || this.nextLineIsError) {
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
        const matchers = /^\s+--\s+(.*)$/g.exec(line);
        if (!matchers && !this.nextLineIsError) {
            return false;
        }
        // matchers should never be null at this point if this.nextLineIsError is false, but the null check can't
        // detect that. Instead, we use the matchers_message constant which ensures matchers is not indexed if null.
        const matchers_message = matchers ? matchers[1] : '';
        const message = this.nextLineIsError ? line : matchers_message;

        if (message.startsWith('Beginning of algorithm string --algorithm not found')) {
            // This error means that there's no PlusCal code in file. Just ignore it.
            return true;
        }

        // If we see the error postfix, we can assume that we have read all error messages
        if (this.nextLineIsError && line.endsWith(ERROR_POSTFIX)) {
            this.nextLineIsError = false;
        }

        // Assume that an empty string message means that the next line is an error. This can happen when the error
        // string looks like: "Unrecoverable error:\n -- \nProcess proc redefined at line 10, column 1\n".
        if (message === '') {
            this.nextLineIsError = true;
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
