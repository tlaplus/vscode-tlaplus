import * as vscode from 'vscode';
import { basename } from 'path';
import * as moment from 'moment';

/**
 * Thrown when there's some problem with parsing.
 */
export class ParsingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

export function pathToUri(path: string): vscode.Uri {
    return vscode.Uri.file(path).with({ scheme: 'file' });
}

export function pathToModuleName(path: string): string {
    const baseName = basename(path);
    const dotIdx = baseName.lastIndexOf('.');
    return dotIdx > 0 ? baseName.substring(0, dotIdx) : baseName;
}

export function parseDateTime(str: string | undefined): moment.Moment | undefined {
    if (!str) {
        return undefined;
    }
    const dateTime = moment(str, moment.ISO_8601, true);
    if (dateTime.isValid) {
        return dateTime;
    }
    throw new ParsingError('Cannot parse date/time ' + str);
}
