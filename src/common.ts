import * as vscode from 'vscode';
import * as moment from 'moment';

export const LANG_TLAPLUS = 'tlaplus';
export const LANG_TLAPLUS_CFG = 'tlaplus_cfg';

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

export function replaceExtension(filePath: string, newExt: string): string {
    const lastDotIdx = filePath.lastIndexOf('.');
    const basePath = lastDotIdx < 0 ? filePath : filePath.substring(0, lastDotIdx);
    return basePath + '.' + newExt;
}

export function parseDateTime(str: string): moment.Moment {
    const dateTime = moment(str, moment.ISO_8601, true);
    if (dateTime.isValid) {
        return dateTime;
    }
    throw new ParsingError('Cannot parse date/time ' + str);
}
