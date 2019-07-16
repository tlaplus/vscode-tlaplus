import * as vscode from 'vscode';
import { ProcessOutputParser } from "../tla2tools";
import { Readable } from "stream";

/**
 * Parses stdout of TLC model checker.
 */
export class TLCModelCheckerStdoutParser extends ProcessOutputParser {
    errMessage: string | null = null;

    constructor(stdout: Readable, filePath: string) {
        super(stdout, filePath);
    }

    protected parseLine(line: string | null) {
        console.log('tlc> ' + (line === null ? ':END:' : line));
    }
}
