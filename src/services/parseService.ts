import * as vscode from 'vscode';
import { DCollection } from '../diagnostic';
import { TranspilerStdoutParser } from '../parsers/pluscal';
import { SanyData, SanyStdoutParser } from '../parsers/sany';
import { ToolOutputChannel } from '../outputChannels';
import { runPlusCal, runSany, stopProcess, ToolProcessInfo } from '../tla2tools';

export class ParseService {
    private readonly plusCalOutChannel = new ToolOutputChannel('PlusCal');
    private readonly sanyOutChannel = new ToolOutputChannel('SANY');

    async parseDocument(document: vscode.TextDocument, token?: vscode.CancellationToken): Promise<DCollection> {
        const messages = await this.transpilePlusCal(document.uri, token);
        const specData = await this.parseSpec(document.uri, token);
        messages.addAll(specData.dCollection);
        return messages;
    }

    async transpilePlusCal(fileUri: vscode.Uri, token?: vscode.CancellationToken): Promise<DCollection> {
        this.throwIfCancelled(token);
        const procInfo = await runPlusCal(fileUri.fsPath);
        this.plusCalOutChannel.bindTo(procInfo);
        const cancellationDisposable = this.registerCancellation(procInfo, token);
        const stdoutParser = new TranspilerStdoutParser(procInfo.mergedOutput, fileUri.fsPath);
        try {
            const result = await stdoutParser.readAll();
            this.throwIfCancelled(token);
            return result;
        } finally {
            cancellationDisposable?.dispose();
        }
    }

    async parseSpec(fileUri: vscode.Uri, token?: vscode.CancellationToken): Promise<SanyData> {
        this.throwIfCancelled(token);
        const procInfo = await runSany(fileUri.fsPath);
        this.sanyOutChannel.bindTo(procInfo);
        const cancellationDisposable = this.registerCancellation(procInfo, token);
        const stdoutParser = new SanyStdoutParser(procInfo.mergedOutput);
        try {
            const result = await stdoutParser.readAll();
            this.throwIfCancelled(token);
            return result;
        } finally {
            cancellationDisposable?.dispose();
        }
    }

    private throwIfCancelled(token: vscode.CancellationToken | undefined): void {
        if (token?.isCancellationRequested) {
            throw new vscode.CancellationError();
        }
    }

    private registerCancellation(
        procInfo: ToolProcessInfo,
        token: vscode.CancellationToken | undefined
    ): vscode.Disposable | undefined {
        if (!token) {
            return undefined;
        }
        const cancel = () => stopProcess(procInfo.process);
        if (token.isCancellationRequested) {
            cancel();
            return undefined;
        }
        return token.onCancellationRequested(cancel);
    }
}
