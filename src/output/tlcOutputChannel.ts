import * as vscode from 'vscode';
import { ProcessOutputHandler } from '../outputHandler';
import { ToolProcessInfo } from '../tla2tools';
import { Readable } from 'stream';

class OutputToOutChannelSender extends ProcessOutputHandler<void> {
    constructor(
        source: Readable | string[],
        private outChannel: vscode.OutputChannel
    ) {
        super(source);
    }

    protected handleLine(line: string | null): void {
        if (line) {
            const cleanLine = line.replace(/@!@!@(START|END)MSG \d+(\:\d+)? @!@!@/g, '');
            if (line.length === 0 || cleanLine.length > 0) {
                this.outChannel.appendLine(line);
            }
        }
    }
}

/**
 * Sends all the TLC output to a special output channel.
 */
export class TlcOutputChannel {
    outChannel: vscode.OutputChannel = vscode.window.createOutputChannel('TLC');
    outSender: OutputToOutChannelSender | undefined;

    bindTo(procInfo: ToolProcessInfo) {
        this.outChannel.clear();
        this.outChannel.appendLine(procInfo.commandLine);
        this.outChannel.appendLine('');
        this.outSender = new OutputToOutChannelSender(procInfo.process.stdout, this.outChannel);
    }

    revealWindow() {
        this.outChannel.show();
    }
}
