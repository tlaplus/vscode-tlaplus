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
    State,
    StateChangeEvent,
    TextDocumentIdentifier,
    TransportKind,
    VersionedTextDocumentIdentifier
} from 'vscode-languageclient/node';
import { TlapsConfigChanged, TlapsProofStepDetails } from './model/tlaps';
import { DelayedFn } from './common';
import {
    InitRequestInItializationOptions,
    InitResponseCapabilitiesExperimental,
} from './model/paths';
import { moduleSearchPaths, TLAPS } from './paths';
import { parseSpec } from './commands/parseModule';
import { SanyData } from './parsers/sany';
import { applyDCollection } from './diagnostic';

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
    private configInitialized = false;
    private configEnabled = false;
    private configCommand = [] as string[];
    private configWholeLine = true;
    private proofStateDecorationTypes = new Map<string, vscode.TextEditorDecorationType>();

    constructor(
        private context: vscode.ExtensionContext,
        private diagnostic: vscode.DiagnosticCollection,
        private currentProofStepDetailsListener: ((details: TlapsProofStepDetails) => void),
        private configChangedListener: ((configChanged: TlapsConfigChanged) => void)
    ) {
        const delayedCurrentProofStepSet = new DelayedFn(500);
        context.subscriptions.push(vscode.window.onDidChangeTextEditorSelection(event => {
            // We track the cursor here to show the current proof step based on the
            // cursor position.
            delayedCurrentProofStepSet.do(() => {
                if (!this.configEnabled) {
                    return;
                }
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
            if (!this.configEnabled || !this.client || !textEditor) {
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
                if (!this.configEnabled) {
                    vscode.window.showInformationMessage(
                        'TLAPS support is disabled.',
                        'Configure'
                    ).then(action => {
                        if (action === 'Configure') {
                            vscode.commands.executeCommand('workbench.action.openSettings', 'tlaplus.tlaps.enabled');
                        }
                    });
                    return;
                }
                if (!this.client) {
                    return;
                }
                this.checkStep(te).catch((err) => {
                    vscode.window.showErrorMessage(`TLAPS proof check failed: ${err}`);
                });
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

    // Runs SANY on the module before forwarding the proof check to TLAPS.
    //
    // TLAPS and SANY do not accept exactly the same language: TLAPS accepts some
    // specifications that SANY (the standard TLA+ front end) correctly rejects.
    // TLAPS accepts "raw TLA" (rTLA), which permits unrestrictive assertions
    // about behaviors that should be unassertable in TLA+, i.e. formulas that
    // are not insensitive to stuttering. Eliminating rTLA is the primary reason
    // for running SANY before TLAPS.
    // To preserve the invariant the TLA+ Toolbox used to enforce, we parse the
    // module with SANY first (reusing the implementation behind `tlaplus.parse`)
    // and only invoke TLAPS if the module is a valid TLA+ module.
    private async checkStep(te: vscode.TextEditor) {
        const document = te.document;
        // SANY and the TLAPS LSP expect file:// documents.
        if (document.uri.scheme !== 'file') {
            vscode.window.showWarningMessage(
                'TLAPS proof checking is only available for TLA+ files saved on disk.'
            );
            return;
        }
        // Capture the selection before any `await`, as it may change meanwhile.
        const selection: Range = {
            start: te.selection.start,
            end: te.selection.end,
        };
        // Persist the buffer so SANY and TLAPS operate on the same content.
        if (document.isDirty && !await document.save()) {
            return;
        }
        let sanyData: SanyData;
        try {
            sanyData = await parseSpec(document.uri);
        } catch (err) {
            // SANY itself failed to run (not a parse error). Let the user decide
            // whether to proceed without the SANY check; default to aborting.
            const continueLabel = 'Run TLAPS anyway';
            const choice = await vscode.window.showErrorMessage(
                `Error parsing module with SANY: ${err}`,
                continueLabel
            );
            if (choice === continueLabel) {
                this.runCheckStep(document, selection);
            }
            return;
        }
        applyDCollection(sanyData.dCollection, this.diagnostic);
        const hasErrors = sanyData.dCollection.getMessages().some(
            (msg) => msg.diagnostic.severity === vscode.DiagnosticSeverity.Error
        );
        if (hasErrors) {
            // SANY's diagnostics already annotate the module (editor markers and
            // the Problems view), so don't invoke TLAPS on an invalid module.
            return;
        }
        this.runCheckStep(document, selection);
    }

    private runCheckStep(document: vscode.TextDocument, selection: Range) {
        if (!this.client) {
            return;
        }
        vscode.commands.executeCommand('tlaplus.tlaps.check-step.lsp',
            {
                uri: document.uri.toString(),
                version: document.version
            } as VersionedTextDocumentIdentifier,
            selection,
        );
    }

    private readConfig(): boolean {
        const config = vscode.workspace.getConfiguration();
        const configEnabled = config.get<boolean>('tlaplus.tlaps.enabled');
        const configCommand = config.get<string[]>('tlaplus.tlaps.lspServerCommand');
        const configWholeLine = config.get<boolean>('tlaplus.tlaps.wholeLine');
        const configChanged = false
            || !this.configInitialized
            || configEnabled !== this.configEnabled
            || JSON.stringify(configCommand) !== JSON.stringify(this.configCommand)
            || configWholeLine !== this.configWholeLine;
        this.configInitialized = true;
        this.configEnabled = !!configEnabled;
        this.configCommand = configCommand ? configCommand : [];
        this.configWholeLine = !!configWholeLine;
        if (configChanged) {
            this.configChangedListener({enabled: this.configEnabled});
        }
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
            initializationOptions: {
                moduleSearchPaths: moduleSearchPaths.getOtherPaths(TLAPS)
            } as InitRequestInItializationOptions
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
        this.context.subscriptions.push(this.client.onDidChangeState((e: StateChangeEvent) => {
            if (e.oldState !== State.Running && e.newState === State.Running && this.client) {
                const initResult = this.client.initializeResult;
                if (!initResult || !initResult.capabilities.experimental) {
                    return;
                }
                const experimental = initResult.capabilities.experimental as InitResponseCapabilitiesExperimental;
                if (!experimental.moduleSearchPaths) {
                    return;
                }
                moduleSearchPaths.setSourcePaths(TLAPS, 'TLA Proof System', experimental.moduleSearchPaths);
            }
        }));
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
                const end = new vscode.Position(marker.range.end.line, marker.range.end.character);
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
