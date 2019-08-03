import { Readable } from 'stream';
import { ProcessOutputParser } from './base';

/**
 * Parses `java -version` output.
 */
export class JavaVersionParser extends ProcessOutputParser<string | undefined> {

    constructor(source: Readable | string[]) {
        super(source, undefined);
    }

    protected parseLine(line: string | null): void {
        if (!line) {
            return;
        }
        const rxVersion = /version "(.+)"/g;
        const matches = rxVersion.exec(line);
        if (matches) {
            this.result = matches[1];
        }
    }
}
