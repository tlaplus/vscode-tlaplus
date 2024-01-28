// TODO: Click on the proof gutter icons.
//  - https://github.com/microsoft/vscode/issues/5455
//  - https://github.com/microsoft/vscode/issues/175945#issuecomment-1466438453
//
// TODO: Tree View to show the proof.
//  - https://code.visualstudio.com/api/extension-guides/tree-view
//  - https://github.com/microsoft/vscode/issues/103403
//
// TODO: Links to the proof steps: DocumentLinkProvider<T>
//
import * as vscode from 'vscode';
import {
    DocumentUri,
    Executable,
    LanguageClient,
    LanguageClientOptions,
    Range,
    TextDocumentIdentifier,
    TransportKind,
    VersionedTextDocumentIdentifier
} from 'vscode-languageclient/node';
import { TlapsProofStepDetails } from './model/tlaps';
import { DelayedFn } from './common';

export enum proofStateNames {
    proved = 'proved',
    failed = 'failed',
    omitted = 'omitted',
    missing = 'missing',
    pending = 'pending',
    progress = 'progress',
}

export type ProofStateIcons = {
    [key: string]: string;
}

export const proofStateIcons = {
    proved: 'resources/images/icons-material/check_circle_FILL0_wght400_GRAD0_opsz24-color.svg',
    failed: 'resources/images/icons-material/close_FILL0_wght400_GRAD0_opsz24-color.svg',
    omitted: 'resources/images/icons-material/editor_choice_FILL0_wght400_GRAD0_opsz24-color.svg',
    missing: 'resources/images/icons-material/check_box_outline_blank_FILL0_wght400_GRAD0_opsz24-color.svg',
    pending: 'resources/images/icons-material/help_FILL0_wght400_GRAD0_opsz24-color.svg',
    progress: 'resources/images/icons-material/more_horiz_FILL0_wght400_GRAD0_opsz24-color.svg',
} as ProofStateIcons;

interface ProofStepMarker {
    status: string;
    range: Range;
    hover: string;
}

export class TlapsClient {
    private client: LanguageClient | undefined;
    private configEnabled = false;
    private configCommand = [] as string[];
    private configWholeLine = true;
    private proofStateDecorationTypes = new Map<string, vscode.TextEditorDecorationType>();

    constructor(
        private context: vscode.ExtensionContext,
        private currentProofStepDetailsListener: ((details: TlapsProofStepDetails) => void),
    ) {
        const delayedCurrentProofStepSet = new DelayedFn(500);
        context.subscriptions.push(vscode.window.onDidChangeTextEditorSelection(event => {
            // We track the cursor here to show the current proof step based on the
            // cursor position.
            delayedCurrentProofStepSet.do(() => {
                vscode.commands.executeCommand('tlaplus.tlaps.currentProofStep.set.lsp',
                    {
                        uri: event.textEditor.document.uri.toString()
                    } as TextDocumentIdentifier,
                    {
                        start: event.textEditor.selection.start,
                        end: event.textEditor.selection.end
                    } as Range,
                );
            });
        }));
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
                    } as Range,
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
        Object.values(proofStateNames).forEach(name => {
            const color = { 'id': 'tlaplus.tlaps.proofState.' + name };
            const bgColor = name === 'failed' ? { backgroundColor: color } : undefined;
            const decTypeFirst = vscode.window.createTextEditorDecorationType({
                overviewRulerColor: color,
                overviewRulerLane: vscode.OverviewRulerLane.Right,
                light: bgColor,
                dark: bgColor,
                isWholeLine: this.configWholeLine,
                rangeBehavior: vscode.DecorationRangeBehavior.ClosedOpen,
                gutterIconPath: this.context.asAbsolutePath(proofStateIcons[name]),
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
            this.currentProofStepDetailsListener
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
            if (editor.document.uri.toString() !== uri) {
                return;
            }
            const decorations = new Map<string, vscode.DecorationOptions[]>();
            this.proofStateDecorationTypes.forEach((_, decTypeName) => {
                decorations.set(decTypeName, [] as vscode.DecorationOptions[]);
            });
            markers.forEach(marker => {
                const start = new vscode.Position(marker.range.start.line, marker.range.start.character);
                const end = new vscode.Position(marker.range.start.line, marker.range.end.character);
                const range = new vscode.Range(start, end);
                if (marker.range.start.line === marker.range.end.line) {
                    decorations.get(marker.status + '.first')?.push({
                        range: range,
                        hoverMessage: marker.hover,
                    });
                } else {
                    const midA = new vscode.Position(start.line, 1024);
                    const midB = new vscode.Position(start.line + 1, 0);
                    const rangeFirst = new vscode.Range(start, midA);
                    const rangeNext = new vscode.Range(midB, end);
                    decorations.get(marker.status + '.first')?.push({
                        range: rangeFirst,
                        hoverMessage: marker.hover,
                    });
                    decorations.get(marker.status + '.next')?.push({
                        range: rangeNext,
                        hoverMessage: marker.hover,
                    });
                }
            });
            this.proofStateDecorationTypes.forEach((decoratorType, decTypeName) => {
                const decs = decorations.get(decTypeName);
                editor.setDecorations(decoratorType, decs ? decs : []);
            });
        });
    }
}
