import * as vscode from 'vscode';
import { Readable } from 'stream';
import { ParsingError } from '../common';
import { DCollection } from '../diagnostic';

/**
 * Auxiliary class that reads chunks from the given stream or array, breaks data into lines
 * and sends them to the parsing method line by line.
 */
export abstract class ProcessOutputParser<T> {
    protected result: T;
    private closed: boolean = false;
    private buf: string | null = null;
    private resolve?: (result: T) => void;
    private lines: string[] | undefined;

    constructor(source: Readable | string[], initialResult: T) {
        if (source instanceof Readable) {
            const me = this;
            source.on('data', chunk => me.handleData(chunk));
            source.on('end', () => me.handleData(null));
        } else {
            this.lines = source;
        }
        this.result = initialResult;
    }

    /**
     * Reads the stream to the end, parsing all the lines.
     */
    async readAll(): Promise<T> {
        const me = this;
        return new Promise(resolve => {
            me.resolve = resolve;
        });
    }

    /**
     * Parses the source synchronously.
     * For this method to work, the source of the lines must be an array of l.
     */
    readAllSync(): T {
        if (!this.lines) {
            throw new ParsingError('Cannot parse synchronously because the source is not a set of lines');
        }
        this.lines.forEach(l => {
            this.tryParseLine(l);
        });
        this.tryParseLine(null);
        if (!this.result) {
            throw new Error('No parsing result returned');
        }
        return this.result;
    }

    protected abstract parseLine(line: string | null): void;

    protected handleError(err: any) {
        // Do nothing by default
    }

    private handleData(chunk: Buffer | string | null) {
        if (this.closed) {
            throw new Error('Stream is closed.');
        }
        if (chunk === null) {
            // console.log(':END:');
            this.tryParseLine(this.buf);
            this.buf = null;
            this.closed = true;
            if (this.resolve) {
                this.resolve(this.result);
            }
            return;
        }
        const str = String(chunk);
        const eChunk = this.buf === null ? str : this.buf + str;
        const lines = eChunk.split('\n');
        if (str.endsWith('\n')) {
            this.buf = null;
            lines.pop();
        } else {
            this.buf = lines.pop() || null;
        }
        const me = this;
        lines.forEach(line => {
            // console.log('> ' + line);
            me.tryParseLine(line);
        });
    }

    private tryParseLine(line: string | null) {
        try {
            this.parseLine(line);
        } catch (err) {
            this.handleError(err);
            console.error(`Error parsing output line: ${err}`);
        }
    }
}

/**
 * Parser that reads output of a TLA+ tool.
 */
export abstract class TLAToolParser extends ProcessOutputParser<DCollection> {

    protected readonly filePath?: string;

    constructor(source: Readable | string[], filePath?: string) {
        super(source, new DCollection());
        this.filePath = filePath;
        if (filePath) {
            this.addDiagnosticFilePath(filePath);
        }
    }

    protected addDiagnosticFilePath(filePath: string) {
        this.result.addFilePath(filePath);
    }

    protected addDiagnosticMessage(filePath: string, range: vscode.Range, text: string) {
        this.result.addMessage(filePath, range, text);
    }

    protected addDiagnosticCollection(dCol: DCollection) {
        dCol.getFilePaths().forEach(fp => this.addDiagnosticFilePath(fp));
        dCol.getMessages().forEach(m => this.result.addMessage(m.filePath, m.diagnostic.range, m.diagnostic.message));
    }
}
