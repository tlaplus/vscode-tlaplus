// cSpell:words tlaplus tlaps tlapm
import * as vscode from 'vscode';
import {
    Executable,
    LanguageClient,
    LanguageClientOptions,
    TransportKind,
    VersionedTextDocumentIdentifier
} from 'vscode-languageclient/node';

export class TlapsClient {
    private client: LanguageClient | undefined;
    private configEnabled = false;
    private configCommand = [] as string[];

    constructor(context: vscode.ExtensionContext) {
        context.subscriptions.push(vscode.commands.registerTextEditorCommand(
            'tlaplus.tlaps.check-step',
            (te, ed, args) => {
                if (!this.client) {
                    return;
                }
                vscode.commands.executeCommand('tlaplus.tlaps.check-step.lsp',
                    {
                        uri: te.document.uri.toString(),
                        version: te.document.version
                    } as VersionedTextDocumentIdentifier,
                    {
                        start: te.selection.start,
                        end: te.selection.end
                    } as vscode.Range,
                );
            }
        ));
        context.subscriptions.push(vscode.workspace.onDidChangeConfiguration(event => {
            if (this.readConfig()) {
                this.tryStop();
                this.tryStart();
            }
        }));
        this.readConfig();
        this.tryStart();
    }

    public deactivate() {
        this.tryStop();
    }

    private readConfig(): boolean {
        const config = vscode.workspace.getConfiguration();
        const configEnabled = config.get<boolean>('tlaplus.tlaps.enabled');
        const configCommand = config.get<string[]>('tlaplus.tlaps.lspServerCommand');
        const configChanged =
            configEnabled !== this.configEnabled ||
            JSON.stringify(configCommand) !== JSON.stringify(this.configCommand);
        if (configChanged) {
            console.log('TLAPS config changed, enabled=', configEnabled, 'command=', configCommand);
        }
        this.configEnabled = !!configEnabled;
        this.configCommand = configCommand ? configCommand : [];
        return configChanged;
    }

    private tryStart() {
        console.log('TODO: TLAPS LSP -- 1');
        if (this.client) {
            return; // Already started.
        }
        console.log('TODO: TLAPS LSP -- 2');
        if (!this.configEnabled) {
            return;
        }
        console.log('TODO: TLAPS LSP -- 3');
        const lspServerCommand = this.configCommand;
        if (!lspServerCommand || lspServerCommand.length === 0) {
            return;
        }
        const command = lspServerCommand[0];
        const cmdArgs = lspServerCommand.slice(1);
        console.log('TODO: TLAPS LSP -- 4');
        const serverOptions: Executable = {
            command: command,
            transport: TransportKind.stdio,
            args: cmdArgs
        };
        const clientOptions: LanguageClientOptions = {
            documentSelector: [{ scheme: 'file', language: 'tlaplus' }],
        };
        this.client = new LanguageClient(
            'tlaplus.tlaps.lsp',
            'TLA+ Proof System',
            serverOptions,
            clientOptions,
            true,
        );
        this.client.start();
        console.log('TLAPS LSP server started.');
    }

    private tryStop() {
        const client = this.client;
        this.client = undefined;
        if (!client) {
            return undefined;
        }
        console.log('TLAPS LSP server is going to stop.');
        return client.stop();
    }
}
