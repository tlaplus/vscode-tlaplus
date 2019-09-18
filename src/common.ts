import * as vscode from 'vscode';
import * as moment from 'moment';
import * as path from 'path';
import { tmpdir } from 'os';
import { existsSync, mkdirSync, readdirSync, unlink, rmdir } from 'fs';

export const LANG_TLAPLUS = 'tlaplus';
export const LANG_TLAPLUS_CFG = 'tlaplus_cfg';
const MAX_TEMP_DIR_ATTEMPTS = 100;

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

export function createTempDirSync(): string | undefined {
    const baseDir = tmpdir();
    for (let i = 0; i < MAX_TEMP_DIR_ATTEMPTS; i++) {
        const timestamp = new Date().getTime();
        const tempDir = `${baseDir}${path.sep}vscode-tlaplus-${timestamp}`;
        if (!existsSync(tempDir)) {
            mkdirSync(tempDir);
            return tempDir;
        }
    }
    vscode.window.showErrorMessage(`Cannot create temporary directory inside ${baseDir}.`);
    return undefined;
}

export async function deleteDir(dirPath: string) {
    for (const fileName of readdirSync(dirPath)) {
        const filePath = path.join(dirPath, fileName);
        try {
            await deleteFile(filePath);
        } catch (err) {
            console.error(`Cannot delete file ${filePath}: ${err}`);
        }
    }
    rmdir(dirPath, (err) => {
        if (err) {
            console.error(`Cannot delete directory ${dirPath}: ${err}`);
        }
    });
}

async function deleteFile(filePath: string): Promise<any | null> {
    return new Promise((resolve, reject) => {
        unlink(filePath, (err) => {
            if (err) {
                reject(err);
                return;
            }
            resolve(null);
        });
    });
}
