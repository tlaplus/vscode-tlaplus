import * as vscode from 'vscode';
import {
    DocumentUri,
    Executable,
    LanguageClient,
    LanguageClientOptions,
    TransportKind,
    VersionedTextDocumentIdentifier
} from 'vscode-languageclient/node';

interface ProofStateMarker {
    range: vscode.Range;
    state: string;
    hover: string;
}

export class TlapsClient {
    private client: LanguageClient | undefined;
    private configEnabled = false;
    private configCommand = [] as string[];
    private proofStateNames = [
        'proved',
        'failed',
        'omitted',
        'missing',
        'pending',
        'progress',
    ];
    private proofStateDecorationTypes = new Map<string, vscode.TextEditorDecorationType>(
        this.proofStateNames.map(name => {
            const color = { 'id': 'tlaplus.tlaps.proofState.' + name };
            const decType = vscode.window.createTextEditorDecorationType({
                overviewRulerColor: color,
                overviewRulerLane: vscode.OverviewRulerLane.Right,
                light: { backgroundColor: color },
                dark: { backgroundColor: color },
                isWholeLine: true,
                rangeBehavior: vscode.DecorationRangeBehavior.ClosedClosed,
            });
            return [name, decType];
        })
    );

    constructor(private context: vscode.ExtensionContext) {
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
        this.configEnabled = !!configEnabled;
        this.configCommand = configCommand ? configCommand : [];
        return configChanged;
    }

    private tryStart() {
        if (this.client) {
            return; // Already started.
        }
        if (!this.configEnabled) {
            return;
        }
        const lspServerCommand = this.configCommand;
        if (!lspServerCommand || lspServerCommand.length === 0) {
            return;
        }
        const command = lspServerCommand[0];
        const cmdArgs = lspServerCommand.slice(1);
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
        this.context.subscriptions.push(this.client.onNotification(
            'tlaplus/tlaps/proofStates',
            this.proofStateNotifHandler.bind(this)
        ));
        this.client.start();
    }

    private tryStop() {
        const client = this.client;
        this.client = undefined;
        if (!client) {
            return undefined;
        }
        return client.stop();
    }

    private proofStateNotifHandler(uri: DocumentUri, markers: ProofStateMarker[]) {
        vscode.window.visibleTextEditors.forEach(editor => {
            if (editor.document.uri.toString() === uri) {
                const decorations = new Map(this.proofStateNames.map(name => [name, [] as vscode.DecorationOptions[]]));
                markers.forEach(marker => {
                    decorations.get(marker.state)?.push(
                        {
                            range: marker.range,
                            hoverMessage: marker.hover,
                        }
                    );
                });
                this.proofStateDecorationTypes.forEach((decoratorType, proofStateName) => {
                    const decs = decorations.get(proofStateName);
                    editor.setDecorations(decoratorType, decs ? decs : []);
                });
            }
        });
    }
}
