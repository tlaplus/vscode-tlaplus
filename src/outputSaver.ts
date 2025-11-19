import * as vscode from 'vscode';
import * as fs from 'fs';
import { basename } from 'path';
import { Readable } from 'stream';

const OPEN_MODE = fs.constants.O_WRONLY | fs.constants.O_CREAT | fs.constants.O_TRUNC;

class StreamWriter {
    constructor(public fd: number | undefined) {}
}

/**
 * Writes all the data from a stream to the given file.
 */
export function saveStreamToFile(src: Readable | null, filePath: string): void {
    fs.open(filePath, OPEN_MODE, (err, fd) => {
        if (err) {
            const fileName = basename(filePath);
            vscode.window.showWarningMessage(`Cannot open file ${fileName}: ${err}`);
            return;
        }
        const sw = new StreamWriter(fd);
        src?.on('data', (data) => writeToFile(sw, data));
        src?.on('end', () => closeFile(sw));
        src?.on('error', (err) => {
            vscode.window.showWarningMessage(`Error reading process output: ${err}`);
            closeFile(sw);
        });
    });
}

function writeToFile(sw: StreamWriter, chunk: Buffer | string) {
    if (!sw.fd) {
        return;
    }
    fs.write(sw.fd, Buffer.from(chunk), (err) => {
        if (err) {
            vscode.window.showWarningMessage(`Error writing .out file: ${err}`);
            closeFile(sw);
        }
    });
}

function closeFile(sw: StreamWriter) {
    if (!sw.fd) {
        return;
    }
    fs.close(sw.fd, (err) => {
        sw.fd = undefined;
        if (err) {
            vscode.window.showWarningMessage(`Error closing .out file: ${err}`);
        }
    });
}
