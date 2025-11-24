import { Readable } from 'stream';
import { ParsingError } from './common';

const CHAR_RETURN = 13;

/**
 * Auxiliary class that reads chunks from the given stream or array, breaks data into lines
 * and sends them to the handling method line by line.
 */
export abstract class ProcessOutputHandler<T> {
    protected result: T;
    private closed = false;
    private buf: string | null = null;
    private resolve?: (result: T) => void;
    private reject?: (err: unknown) => void;
    private readonly lines: string[] | undefined;

    constructor(source: Readable | string[] | null, initialResult: T) {
        if (source instanceof Readable) {
            source.on('data', chunk => this.handleData(chunk));
            source.on('end', () => this.handleData(null));
            source.on('error', err => this.handleSourceError(err));
        } else {
            this.lines = source === null ? [] : source;
        }
        this.result = initialResult;
    }

    /**
     * Reads the stream to the end, parsing all the lines.
     */
    async readAll(): Promise<T> {
        return new Promise((resolve, reject) => {
            this.resolve = resolve;
            this.reject = reject;
        });
    }

    /**
     * Handles the source synchronously.
     * For this method to work, the source of the lines must be an array of l.
     */
    readAllSync(): T {
        if (!this.lines) {
            throw new ParsingError('Cannot handle synchronously because the source is not a set of lines');
        }
        this.lines.forEach(l => {
            this.tryHandleLine(l);
        });
        this.tryHandleLine(null);
        if (!this.result) {
            throw new Error('No handling result returned');
        }
        return this.result;
    }

    protected abstract handleLine(line: string | null): void;

    protected handleError(err: unknown): void {
        // Do nothing by default
    }

    private handleData(chunk: Buffer | string | null) {
        if (this.closed) {
            return;
        }
        if (chunk === null) {
            this.tryHandleLine(this.buf);
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
        lines.forEach(line => this.tryHandleLine(line));
    }

    private handleSourceError(err: unknown) {
        if (this.closed) {
            return;
        }
        this.closed = true;
        this.handleError(err);
        if (this.reject) {
            this.reject(err);
        }
    }

    private tryHandleLine(line: string | null) {
        try {
            // On Windows, the last 0x0A character is still in the line, cut it off
            const eLine = line && line.charCodeAt(line.length - 1) === CHAR_RETURN
                ? line.substring(0, line.length - 1)
                : line;
            this.handleLine(eLine);
        } catch (err) {
            this.handleError(err);
            console.error(`Error handling output line: ${err}`);
        }
    }
}
