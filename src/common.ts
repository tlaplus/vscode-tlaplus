import * as vscode from 'vscode';
import * as moment from 'moment';
import * as path from 'path';
import * as fs from 'fs';
import { tmpdir } from 'os';

export const LANG_TLAPLUS = 'tlaplus';
export const LANG_TLAPLUS_CFG = 'tlaplus_cfg';
const MAX_TEMP_DIR_ATTEMPTS = 100;

export const emptyFunc = function(): void {
    return undefined;
};

/**
 * Thrown when there's some problem with parsing.
 */
export class ParsingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

/**
 * Occurs when there's a model checking problem.
 *
 * For example, this error can occur if the checked file is not a TLA+ file and therefore cannot be model checked.
 */
export class ModelCheckingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

export function pathToUri(filePath: string): vscode.Uri {
    return vscode.Uri.file(filePath).with({ scheme: 'file' });
}

export function replaceExtension(filePath: string, newExt: string): string {
    const lastDotIdx = filePath.lastIndexOf('.');
    const basePath = lastDotIdx < 0 ? filePath : filePath.substring(0, lastDotIdx);
    return `${basePath}.${newExt}`;
}

export function parseDateTime(str: string): moment.Moment {
    const dateTime = moment(str, moment.ISO_8601, true);
    if (dateTime.isValid()) {
        return dateTime;
    }
    throw new ParsingError(`Cannot parse date/time ${str}`);
}

export function pathToModuleName(filePath: string): string {
    // It's necessary to check both separators here, not just `path.sep`
    // to support .out files portability. TLA+ doesn't support slashes in module names,
    // so it breaks nothing.
    // path.basename() doesn't work in some cases
    const sid = Math.max(filePath.lastIndexOf('/'), filePath.lastIndexOf('\\'));
    return filePath.substring(sid + 1, filePath.length - 4);   // remove path and .tla
}

export function createTempDirSync(): string | undefined {
    const baseDir = tmpdir();
    for (let i = 0; i < MAX_TEMP_DIR_ATTEMPTS; i++) {
        const timestamp = new Date().getTime();
        const tempDir = `${baseDir}${path.sep}vscode-tlaplus-${timestamp}`;
        if (!fs.existsSync(tempDir)) {
            fs.mkdirSync(tempDir);
            return tempDir;
        }
    }
    vscode.window.showErrorMessage(`Cannot create temporary directory inside ${baseDir}.`);
    return undefined;
}

export async function mkDir(dirPath: string): Promise<void> {
    return new Promise((resolve, reject) => {
        fs.mkdir(dirPath, null, (err) => {
            if (err) {
                reject(err);
                return;
            }
            resolve();
        });
    });
}

export async function deleteDir(dirPath: string): Promise<void> {
    for (const fileName of fs.readdirSync(dirPath)) {
        const filePath = path.join(dirPath, fileName);
        try {
            const fileInfo = await getFileInfo(filePath);
            if (fileInfo.isDirectory()) {
                await deleteDir(filePath);
            } else {
                await deleteFile(filePath);
            }
        } catch (err) {
            console.error(`Cannot delete file ${filePath}: ${err}`);
        }
    }
    fs.rmdir(dirPath, (err) => {
        if (err) {
            console.error(`Cannot delete directory ${dirPath}: ${err}`);
        }
    });
}

async function deleteFile(filePath: string): Promise<void> {
    return new Promise((resolve, reject) => {
        fs.unlink(filePath, (err) => {
            if (err) {
                reject(err);
                return;
            }
            resolve(undefined);
        });
    });
}

async function getFileInfo(filePath: string): Promise<fs.Stats> {
    return new Promise((resolve, reject) => {
        fs.lstat(filePath, (err, stats) => {
            if (err) {
                reject(err);
                return;
            }
            resolve(stats);
        });
    });
}

export async function copyFile(filePath: string, destDir: string): Promise<void> {
    return new Promise((resolve, reject) => {
        const fileName = path.basename(filePath);
        fs.copyFile(filePath, path.join(destDir, fileName), (err) => {
            if (err) {
                reject(err);
                return;
            }
            resolve(undefined);
        });
    });
}

export async function writeFile(filePath: string, ...contents: string[]): Promise<boolean> {
    return new Promise((resolve, reject) => {
        fs.writeFile(filePath, contents.join('\n'), (err) => {
            if (err) {
                reject(err);
            } else {
                resolve(true);
            }
        });
    });
}

export async function readFile(filePath: string): Promise<string> {
    return new Promise((resolve, reject) => {
        fs.readFile(filePath, { encoding: 'UTF-8' }, (err, data) => {
            if (err) {
                reject(err);
            } else {
                resolve(data);
            }
        });
    });
}

export async function listFiles(dirPath: string, predicate?: (name: string) => boolean): Promise<string[]> {
    return new Promise<string[]>((resolve, reject) => {
        fs.readdir(dirPath, (err, files) => {
            if (err) {
                reject(err);
                return;
            }
            const result = predicate ? files.filter(predicate) : files;
            resolve(result);
        });
    });
}

export async function exists(filePath: string): Promise<boolean> {
    return new Promise(resolve => {
        fs.exists(filePath, (ex) => resolve(ex));
    });
}
