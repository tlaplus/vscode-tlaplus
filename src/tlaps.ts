// TODO: Click on the proof gutter icons.
//  - https://github.com/microsoft/vscode/issues/5455
//  - https://github.com/microsoft/vscode/issues/175945#issuecomment-1466438453
//
// TODO: Tree View to show the proof.
//  https://code.visualstudio.com/api/extension-guides/tree-view
//  https://github.com/microsoft/vscode/issues/103403
//  Also show WebviewView to show a custom content in a sidebar.
//
// TODO: Auto re-read proof state for the visible range:
//  - Visible range: https://stackoverflow.com/questions/40339229/vscode-extension-api-how-to-get-only-visible-lines-of-editor
//  - Cursor change event: https://stackoverflow.com/questions/44782075/vscode-extension-ondidchangecursorposition
//
// TODO: Links to the proof steps: DocumentLinkProvider<T>
//
// TODO: Links from the side pane: TextEditor.revealRange(range: Range, revealType?: TextEditorRevealType): void
//
import * as vscode from 'vscode';
import {
    DocumentUri,
    Executable,
    LanguageClient,
    LanguageClientOptions,
    TextDocumentIdentifier,
    TransportKind,
    VersionedTextDocumentIdentifier
} from 'vscode-languageclient/node';
import { TlapsProofObligationView } from './webview/tlapsCurrentProofObligationView';
import { TlapsProofStepDetails } from './model/tlaps';

interface ProofStepMarker {
    status: string;
    range: vscode.Range;
    hover: string;
}

export class TlapsClient {
    private client: LanguageClient | undefined;
    private configEnabled = false;
    private configCommand = [] as string[];
    private configWholeLine = true;
    private proofStateNames = [
        'proved',
        'failed',
        'omitted',
        'missing',
        'pending',
        'progress',
    ];
    private proofStateDecorationTypes = new Map<string, vscode.TextEditorDecorationType>();
    private iconsAdhoc = new Map<string, string>(Object.entries({
        proved: 'icons-adhoc/tlaps-proof-state-proved.svg',
        failed: 'icons-adhoc/tlaps-proof-state-failed.svg',
        omitted: 'icons-adhoc/tlaps-proof-state-omitted.svg',
        missing: 'icons-adhoc/tlaps-proof-state-missing.svg',
        pending: 'icons-adhoc/tlaps-proof-state-pending.svg',
        progress: 'icons-adhoc/tlaps-proof-state-progress.svg',
    }));
    private iconsMaterial = new Map<string, string>(Object.entries({
        proved: 'icons-material/check_circle_FILL0_wght400_GRAD0_opsz24-color.svg',
        failed: 'icons-material/close_FILL0_wght400_GRAD0_opsz24-color.svg',
        omitted: 'icons-material/editor_choice_FILL0_wght400_GRAD0_opsz24-color.svg',
        missing: 'icons-material/check_box_outline_blank_FILL0_wght400_GRAD0_opsz24-color.svg',
        pending: 'icons-material/help_FILL0_wght400_GRAD0_opsz24-color.svg',
        progress: 'icons-material/more_horiz_FILL0_wght400_GRAD0_opsz24-color.svg',
    }));
    private icons = this.iconsMaterial;

    constructor(
        private context: vscode.ExtensionContext,
        private tlapsProofObligationView: TlapsProofObligationView,
    ) {
        // TODO: Here.
        // context.subscriptions.push(vscode.window.onDidChangeTextEditorSelection(function(e) {
        //     console.log(e);
        // }, this));
        context.subscriptions.push(vscode.window.onDidChangeActiveTextEditor(textEditor => {
            // A document clears all its decorators when it becomes invisible (e.g. user opens another
            // document in other tab). Here we notify the LSP server to resend the markers.
            if (!this.client || !textEditor) {
                return;
            }
            vscode.commands.executeCommand('tlaplus.tlaps.proofStepMarkers.fetch.lsp',
                {
                    uri: textEditor.document.uri.toString()
                } as TextDocumentIdentifier
            );
        }));
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
                this.makeDecoratorTypes();
                this.tryStart();
            }
        }));
        this.readConfig();
        this.makeDecoratorTypes();
        this.tryStart();
    }

    private makeDecoratorTypes() {
        this.proofStateDecorationTypes.clear();
        this.proofStateNames.forEach(name => {
            const color = { 'id': 'tlaplus.tlaps.proofState.' + name };
            const bgColor = name === 'failed' ? { backgroundColor: color } : undefined;
            const decTypeFirst = vscode.window.createTextEditorDecorationType({
                overviewRulerColor: color,
                overviewRulerLane: vscode.OverviewRulerLane.Right,
                light: bgColor,
                dark: bgColor,
                isWholeLine: this.configWholeLine,
                rangeBehavior: vscode.DecorationRangeBehavior.ClosedOpen,
                gutterIconPath: this.context.asAbsolutePath(`resources/images/${this.icons.get(name)}`),
                gutterIconSize: '100%',
            });
            const decTypeNext = vscode.window.createTextEditorDecorationType({
                overviewRulerColor: color,
                overviewRulerLane: vscode.OverviewRulerLane.Right,
                light: bgColor,
                dark: bgColor,
                isWholeLine: this.configWholeLine,
                rangeBehavior: vscode.DecorationRangeBehavior.ClosedOpen,
            });
            this.proofStateDecorationTypes.set(name + '.first', decTypeFirst);
            this.proofStateDecorationTypes.set(name + '.next', decTypeNext);
        });
    }

    public deactivate() {
        this.tryStop();
    }

    private readConfig(): boolean {
        const config = vscode.workspace.getConfiguration();
        const configEnabled = config.get<boolean>('tlaplus.tlaps.enabled');
        const configCommand = config.get<string[]>('tlaplus.tlaps.lspServerCommand');
        const configWholeLine = config.get<boolean>('tlaplus.tlaps.wholeLine');
        const configChanged = false
            || configEnabled !== this.configEnabled
            || JSON.stringify(configCommand) !== JSON.stringify(this.configCommand)
            || configWholeLine !== this.configWholeLine;
        this.configEnabled = !!configEnabled;
        this.configCommand = configCommand ? configCommand : [];
        this.configWholeLine = !!configWholeLine;
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
            'tlaplus/tlaps/proofStepMarkers',
            this.proofStepMarkersNotifHandler.bind(this)
        ));
        this.context.subscriptions.push(this.client.onNotification(
            'tlaplus/tlaps/currentProofStep',
            (tlapsProofStep: TlapsProofStepDetails) => {
                this.tlapsProofObligationView.showProofObligation(tlapsProofStep);
            }
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

    private proofStepMarkersNotifHandler(uri: DocumentUri, markers: ProofStepMarker[]) {
        vscode.window.visibleTextEditors.forEach(editor => {
            if (editor.document.uri.toString() === uri) {
                const decorations = new Map<string, vscode.DecorationOptions[]>();
                this.proofStateDecorationTypes.forEach((_, decTypeName) => {
                    decorations.set(decTypeName, [] as vscode.DecorationOptions[]);
                });
                markers.forEach(marker => {
                    if (marker.range.isSingleLine) {
                        decorations.get(marker.status + '.first')?.push(
                            {
                                range: marker.range,
                                hoverMessage: marker.hover,
                            }
                        );
                    } else {
                        const start = marker.range.start;
                        const midA = new vscode.Position(start.line, 1024);
                        const midB = new vscode.Position(start.line + 1, 0);
                        const end = marker.range.end;
                        const rangeFirst = new vscode.Range(start, midA);
                        const rangeNext = new vscode.Range(midB, end);
                        decorations.get(marker.status + '.first')?.push(
                            {
                                range: rangeFirst,
                                hoverMessage: marker.hover,
                            }
                        );
                        decorations.get(marker.status + '.next')?.push(
                            {
                                range: rangeNext,
                                hoverMessage: marker.hover,
                            }
                        );
                    }
                });
                this.proofStateDecorationTypes.forEach((decoratorType, decTypeName) => {
                    const decs = decorations.get(decTypeName);
                    editor.setDecorations(decoratorType, decs ? decs : []);
                });
            }
        });
    }
}
