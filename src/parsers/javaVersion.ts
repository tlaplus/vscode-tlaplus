import { Readable } from 'stream';
import { ProcessOutputHandler } from '../outputHandler';
import { JavaVersion } from '../tla2tools';

/**
 * Parses `java -version` output.
 */
export class JavaVersionParser extends ProcessOutputHandler<JavaVersion> {
    private version: string = JavaVersion.UNKNOWN_VERSION;
    private outLines: string[] = [];

    constructor(source: Readable | string[]) {
        super(source, new JavaVersion(JavaVersion.UNKNOWN_VERSION, []));
    }

    protected handleLine(line: string | null): void {
        if (line === null) {
            this.result = new JavaVersion(this.version, this.outLines);
            return;
        }
        this.outLines.push(line);
        if (this.version !== JavaVersion.UNKNOWN_VERSION) {
            return;
        }
        const rxVersion = /version "(.+)"/g;
        const matches = rxVersion.exec(line);
        if (matches) {
            this.version = matches[1];
        }
    }
}
