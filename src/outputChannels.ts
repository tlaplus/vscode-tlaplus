import * as vscode from 'vscode';
import { ProcessOutputHandler } from './outputHandler';
import { ToolProcessInfo } from './tla2tools';
import { Readable } from 'stream';

type LineMapper = (line: string) => string | undefined;

class OutputToOutChannelSender extends ProcessOutputHandler<void> {
    constructor(
        source: Readable | string[],
        private outChannel: vscode.OutputChannel,
        private lineMapper: LineMapper | undefined
    ) {
        super(source);
    }

    protected handleLine(line: string | null): void {
        if (!line) {
            return;
        }
        const eLine = this.lineMapper ? this.lineMapper(line) : line;
        if (eLine) {
            this.outChannel.appendLine(eLine);
        }
    }
}

/**
 * Manages an output channel and sends output of tool processes to that channel.
 */
export class ToolOutputChannel {
    outChannel: vscode.OutputChannel;
    outSender: ProcessOutputHandler<void> | undefined;
    lineMapper: LineMapper | undefined;

    constructor(name: string, lineMapper?: LineMapper) {
        this.outChannel = vscode.window.createOutputChannel(name);
        this.lineMapper = lineMapper;
    }

    bindTo(procInfo: ToolProcessInfo) {
        this.outChannel.clear();
        this.outChannel.appendLine(procInfo.commandLine);
        this.outChannel.appendLine('');
        this.outSender = new OutputToOutChannelSender(procInfo.process.stdout, this.outChannel, this.lineMapper);
    }

    revealWindow() {
        this.outChannel.show();
    }

    clear() {
        this.outChannel.clear();
    }

    appendLine(line: string) {
        this.outChannel.appendLine(line);
    }
}
