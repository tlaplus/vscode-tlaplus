import * as vscode from 'vscode';
import * as moment from 'moment';
import { basename } from 'path';

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

export function pathToModuleName(filePath: string): string {
    // It's necessary to check both separators here, not just `path.sep`
    // to support .out files portability. TLA+ doesn't support slashes in module names,
    // so it breaks nothing.
    // path.basename() doesn't work in some cases
    const sid = Math.max(filePath.lastIndexOf('/'), filePath.lastIndexOf('\\'));
    const modName = filePath.substring(sid + 1, filePath.length - 4);   // remove path and .tla
    return modName;
}
