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
    private nowParsingAddedLabels = false; // TODO should the parser be a state machine?

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

        this.tryParseAddedLabels(line);
    }

    private tryParseUnrecoverableError(line: string): boolean {
        const matchers = /^\s+--\s+(.*)$/g.exec(line);
        if (!matchers && !this.nextLineIsError) {
            return false;
        }
        // matchers should never be null at this point if this.nextLineIsError is false, but the null check can't
        // detect that. Instead, we use the matchersMessage constant which ensures matchers is not indexed if null.
        const matchersMessage = matchers ? matchers[1] : '';
        const message = this.nextLineIsError ? line : matchersMessage;

        if (message.startsWith('Beginning of algorithm string --algorithm not found')) {
            // This error means that there's no PlusCal code in file. Just ignore it.
            return true;
        }

        // If we see the error postfix, we can assume that we have read all error messages
        if (this.nextLineIsError && line.endsWith(ERROR_POSTFIX)) {
            this.nextLineIsError = false;
        }

        // Assume that an empty string message that matches the regex means that the next line is an error. This can
        // happen when the error string looks like:
        // "Unrecoverable error:\n -- \nProcess proc redefined at line 10, column 1\n".
        if (message === '' && matchers) {
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

    /**
     * Adds info on labels added by the pluscal translated.
     *
     * Only takes effect if the `-reportLabels` was added to PlusCal options. Output looks like:
     *
     *       The following labels were added: // 1
     *           Lbl_1 at line 16, column 5
     *           Lbl_2 at line 23, column 9
     *
     *
     * So we can start looking for labels as soon as we see (1)
     * and stop as soon as we stop seeing label strings.
     *
     */
    private tryParseAddedLabels(line: string) {
        // https://github.com/tlaplus/tlaplus/blob/21f92/tlatools/org.lamport.tlatools/src/pcal/ParseAlgorithm.java#L668
        const addStartPrefixes = ['The following labels were added:', 'The following label was added:'];
        if (addStartPrefixes.some(prefix => line.startsWith(prefix))) {
            this.nowParsingAddedLabels = true;
            return true;
        }
        if (!this.nowParsingAddedLabels) {
            return false;
        }

        const matcher = /^\s\s([A-Za-z0-9_]+) at line \d+, column \d+/g.exec(line); // no closing `$` to handle macro statements
        if (!matcher) { // done parsing
            this.nowParsingAddedLabels = false;
            return false;
        }

        const labelname = matcher[1];
        const message = `Missing label, translator inserted \`${labelname}\` here`;
        const locInfo = this.parseLabelLocation(line) || ZERO_LOCATION_INFO;
        const locRange = new vscode.Range(locInfo.location, locInfo.location);
        this.result.addMessage(this.filePath, locRange, message, vscode.DiagnosticSeverity.Information);

        return true;
    }

    /**
     * Extracts location info from PlusCal translation strings.
     * Note: not robust for labels. Use parseLabelLocation instead.
     */
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

    /**
     * Extracts label location info from label added strings.
     * Similar to `parseLocation`, EXCEPT it's also robust against insertions due to macros:
     *
     *         Lbl_2 at line 1, column 2 of macro called at line 23, column 5
     *
     * In this case, we want to capture "line 23, column 5" NOT "line 1".
     */

    private parseLabelLocation(line: string): LocationInfo | undefined {
        const rxLocation = /\s*(?:at )?line (\d+), column (\d+)(?: of macro called at line (\d+), column (\d+))?.?\s*$/g;
        const matches = rxLocation.exec(line);
        if (!matches) {
            return undefined;
        }

        // get macro match if it exists, otherwise get label match
        const matchLine = matches[3] || matches[1];
        const matchCol = matches[4] || matches[2];

        const posLine = parseInt(matchLine) - 1;
        const posCol = parseInt(matchCol);

        return new LocationInfo(new vscode.Position(posLine, posCol), matches[0].length);
    }
}
