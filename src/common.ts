import * as vscode from 'vscode';
import { basename } from 'path';
import * as dt from 'date-and-time';

/**
 * Thrown when there's some problem with parsing.
 */
export class ParsingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

export function pathToUri(path: string): vscode.Uri {
    return vscode.Uri.parse('file://' + path);
}

export function pathToModuleName(path: string): string {
    const baseName = basename(path);
    const dotIdx = baseName.lastIndexOf('.');
    return dotIdx > 0 ? baseName.substring(0, dotIdx) : baseName;
}

export function parseDateTime(str: string | undefined): Date | undefined {
    if (!str) {
        return undefined;
    }
    const dateTime = dt.parse(str, 'YYYY-MM-DD HH:mm:ss');
    if (dateTime instanceof Date) {
        return dateTime;
    }
    throw new ParsingError('Cannot parse date/time ' + dateTime);
}
