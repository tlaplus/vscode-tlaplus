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
    outChannel: vscode.OutputChannel | undefined;
    outSender: ProcessOutputHandler<void> | undefined;
    lineMapper: LineMapper | undefined;

    constructor(readonly name: string, lineMapper?: LineMapper) {
        this.lineMapper = lineMapper;
    }

    bindTo(procInfo: ToolProcessInfo): void {
        const channel = this.getChannel();
        channel.clear();
        channel.appendLine(procInfo.commandLine);
        channel.appendLine('');
        this.outSender = new OutputToOutChannelSender(procInfo.process.stdout, channel, this.lineMapper);
    }

    revealWindow(): void {
        this.getChannel().show();
    }

    clear(): void {
        this.getChannel().clear();
    }

    appendLine(line: string): void {
        this.getChannel().appendLine(line);
    }

    private getChannel(): vscode.OutputChannel {
        if (!this.outChannel) {
            this.outChannel = vscode.window.createOutputChannel(this.name);
        }
        return this.outChannel;
    }
}
