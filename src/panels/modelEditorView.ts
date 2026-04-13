import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { replaceExtension } from '../common';
import { getNonce } from './utilities/getNonce';
import { getUri } from './utilities/getUri';
import {
    buildModelEditorPaths,
    DEFAULT_TLC_OPTIONS,
    discoverSpecInfo,
    parseModelEditorState,
    serializeModelEditorState,
    tlcOptionsToArgs,
    tlcOptionsManagedFlags,
    ModelEditorState,
    TlcOptionsState
} from '../model/modelEditorFiles';
import { doCheckModel, getSpecFiles } from '../commands/checkModel';
import { revealEmptyCheckResultView } from './checkResultView';

const modelEditorDiagnostics = vscode.languages.createDiagnosticCollection(
    'tlaplus-model-editor'
);

export const CMD_MODEL_EDITOR_DISPLAY = 'tlaplus.model.editor.display';
export const MODEL_EDITOR_VIEW_TYPE = 'tlaplus.cfgEditor';
const CFG_MODEL_EDITOR_ENABLED = 'tlaplus.modelEditor.enabled';

function isModelEditorEnabled(): boolean {
    return vscode.workspace.getConfiguration()
        .get<boolean>(CFG_MODEL_EDITOR_ENABLED, false);
}

export function showModelEditor(
    context: vscode.ExtensionContext,
    uri?: vscode.Uri
): void {
    if (!isModelEditorEnabled()) {
        vscode.window.showInformationMessage(
            'The Model Editor is experimental. Enable it via '
            + '`tlaplus.modelEditor.enabled` in settings.',
            'Open Settings'
        ).then((choice) => {
            if (choice === 'Open Settings') {
                void vscode.commands.executeCommand(
                    'workbench.action.openSettings',
                    CFG_MODEL_EDITOR_ENABLED
                );
            }
        });
        return;
    }

    const fileUri = uri ?? vscode.window.activeTextEditor?.document.uri;
    if (!fileUri) {
        vscode.window.showWarningMessage(
            'No TLA+ specification file is open.'
        );
        return;
    }

    if (fileUri.fsPath.endsWith('.cfg')) {
        void vscode.commands.executeCommand(
            'vscode.openWith', fileUri, MODEL_EDITOR_VIEW_TYPE
        );
        return;
    }

    // If the user opened an MC file, resolve to the underlying spec
    const resolvedUri = resolveSpecUri(fileUri);
    ModelEditorPanel.createOrReveal(context, resolvedUri);
}

/**
 * CustomTextEditorProvider for .cfg files, enabling
 * "Reopen Editor With..." → TLA+ Model Editor.
 */
export class ModelEditorCfgProvider implements vscode.CustomTextEditorProvider {

    constructor(private readonly extContext: vscode.ExtensionContext) {}

    public resolveCustomTextEditor(
        document: vscode.TextDocument,
        webviewPanel: vscode.WebviewPanel
    ): void {
        if (!isModelEditorEnabled()) {
            webviewPanel.webview.html = '<p>Enable '
                + '<code>tlaplus.modelEditor.enabled</code> '
                + 'in settings to use the Model Editor.</p>';
            return;
        }
        const cfgPath = document.uri.fsPath;
        const specPath = resolveSpecPathFromCfg(cfgPath);
        setupModelEditorWebview(
            webviewPanel, this.extContext, () => specPath
        );
    }
}


interface WebviewSetup {
    disposables: vscode.Disposable[];
    sendInitData: () => Promise<void>;
}

function setupModelEditorWebview(
    panel: vscode.WebviewPanel,
    extContext: vscode.ExtensionContext,
    getSpecPath: () => string
): WebviewSetup {
    const disposables: vscode.Disposable[] = [];
    const extensionUri = extContext.extensionUri;

    panel.webview.options = {
        enableScripts: true,
        localResourceRoots: [vscode.Uri.joinPath(extensionUri, 'out')]
    };
    panel.webview.html = getWebviewHtml(panel.webview, extensionUri);

    const sendInitData = async () => {
        const initPayload = await buildInitPayload(getSpecPath());
        void panel.webview.postMessage({
            type: 'init', data: initPayload
        });
    };

    panel.webview.onDidReceiveMessage(
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        (message: any) => {
            if (message.command === 'ready') {
                void sendInitData();
            } else if (message.command === 'saveModel') {
                saveModelFiles(
                    panel, message.state as ModelEditorState,
                    message.tlcOptions as
                        TlcOptionsState | undefined
                );
            } else if (message.command === 'saveAndRun') {
                const st = message.state as ModelEditorState;
                const tlcOpts = (message.tlcOptions
                    ?? DEFAULT_TLC_OPTIONS) as TlcOptionsState;
                if (saveModelFiles(panel, st, tlcOpts)) {
                    void launchTlc(st, tlcOpts, extContext);
                }
            } else if (message.command === 'openFile') {
                const filePath = message.path as string;
                const dir = path.dirname(getSpecPath());
                const mn = sanitizeModelName(
                    (message.modelName as string) ?? ''
                );
                let target: string;
                if (filePath === 'tla' && mn) {
                    target = path.join(dir, `${mn}.tla`);
                } else if (filePath === 'cfg' && mn) {
                    target = path.join(dir, `${mn}.cfg`);
                } else {
                    target = filePath;
                }
                void vscode.window.showTextDocument(
                    vscode.Uri.file(target),
                    { viewColumn: vscode.ViewColumn.One }
                );
            }
        },
        null,
        disposables
    );

    // Watch spec files for edits and push updated discovery info
    let watchedPath = getSpecPath();
    let specSyncTimer: ReturnType<typeof setTimeout> | undefined;
    disposables.push(
        vscode.workspace.onDidChangeTextDocument((e) => {
            const currentPath = getSpecPath();
            if (currentPath !== watchedPath) {
                if (specSyncTimer) {
                    clearTimeout(specSyncTimer);
                    specSyncTimer = undefined;
                }
                watchedPath = currentPath;
            }
            if (e.document.uri.fsPath !== currentPath) {
                return;
            }
            if (specSyncTimer) { clearTimeout(specSyncTimer); }
            specSyncTimer = setTimeout(() => {
                const text = e.document.getText();
                const discovered = discoverSpecInfo(text);
                void panel.webview.postMessage({
                    type: 'specUpdated', discovered
                });
            }, 500);
        })
    );

    disposables.push({
        dispose: () => {
            if (specSyncTimer) { clearTimeout(specSyncTimer); }
        }
    });

    return { disposables, sendInitData };
}

async function buildInitPayload(specPath: string) {
    const paths = buildModelEditorPaths(specPath);

    // Read the spec from VS Code's document model if open (picks up
    // unsaved edits), otherwise fall back to disk.
    let specText = '';
    const specUri = vscode.Uri.file(specPath);
    const openDoc = vscode.workspace.textDocuments.find(
        (d) => d.uri.fsPath === specUri.fsPath
    );
    if (openDoc) {
        specText = openDoc.getText();
    } else {
        try {
            specText = fs.readFileSync(specPath, 'utf-8');
        } catch { /* */ }
    }

    const discovered = discoverSpecInfo(specText);

    let tlaContent = '';
    let cfgContent = '';
    try {
        tlaContent = fs.readFileSync(paths.tlaFilePath, 'utf-8');
    } catch { /* */ }
    try {
        cfgContent = fs.readFileSync(paths.cfgFilePath, 'utf-8');
    } catch { /* */ }

    const parsed = (tlaContent || cfgContent)
        ? parseModelEditorState(specPath, tlaContent, cfgContent)
        : undefined;

    const existingState = parsed?.state;
    const existingTlcOptions = parsed?.tlcOptions;

    // Merge discovered constants with existing state: keep existing
    // assignments for known constants, add new ones from the spec.
    const mergedConstants = discovered.constants.map((name) => {
        const existing = existingState?.constants.find(
            (c) => c.name === name
        );
        return existing ?? {
            name, kind: 'ordinary' as const, value: ''
        };
    });

    const state: ModelEditorState = existingState
        ? {
            ...existingState,
            specPath,
            specName: paths.specName,
            constants: mergedConstants
        }
        : {
            specName: paths.specName,
            specPath,
            modelName: paths.modelName,
            behavior: {
                kind: 'initNext',
                init: discovered.initCandidates[0] ?? '',
                next: discovered.nextCandidates[0] ?? ''
            },
            checkDeadlock: true,
            constants: mergedConstants,
            invariants: [],
            properties: [],
            stateConstraint: '',
            actionConstraint: '',
            definitionOverrides: [],
            additionalDefinitions: '',
            symmetryConstants: [],
            viewExpression: '',
            alias: '',
            postCondition: ''
        };

    return {
        state, discovered,
        tlcOptions: existingTlcOptions
    };
}

/**
 * Strip path separators and '..' from model names to prevent
 * writing files outside the spec directory.
 */
function sanitizeModelName(name: string): string {
    return name.replace(/[/\\]/g, '').replace(/\.\./g, '');
}

function saveModelFiles(
    panel: vscode.WebviewPanel,
    state: ModelEditorState,
    tlcOptions?: TlcOptionsState
): boolean {
    const dir = path.dirname(state.specPath);
    const safeName = sanitizeModelName(state.modelName);
    const tlaPath = path.join(dir, `${safeName}.tla`);
    const cfgPath = path.join(dir, `${safeName}.cfg`);
    const { tlaContent, cfgContent } = serializeModelEditorState(
        state, tlcOptions
    );

    try {
        fs.writeFileSync(tlaPath, tlaContent, 'utf-8');
        fs.writeFileSync(cfgPath, cfgContent, 'utf-8');
        void panel.webview.postMessage({ type: 'saved' });
        return true;
    } catch (err) {
        void panel.webview.postMessage({
            type: 'error',
            message: `Failed to save model files: ${err}`
        });
        return false;
    }
}

async function launchTlc(
    state: ModelEditorState,
    tlcOpts: TlcOptionsState,
    extContext: vscode.ExtensionContext
): Promise<void> {
    const dir = path.dirname(state.specPath);
    const safeName = sanitizeModelName(state.modelName);
    const tlaPath = path.join(dir, `${safeName}.tla`);
    const uri = vscode.Uri.file(tlaPath);
    const specFiles = await getSpecFiles(uri, true, false);
    if (!specFiles) {
        vscode.window.showWarningMessage(
            'Cannot find model files. Save first.'
        );
        return;
    }
    modelEditorDiagnostics.clear();
    revealEmptyCheckResultView(extContext);
    const extraOpts = tlcOptionsToArgs(tlcOpts);
    await doCheckModel(
        specFiles, true, extContext, modelEditorDiagnostics,
        false, extraOpts, undefined, tlcOptionsManagedFlags()
    );
}

/**
 * Given a .cfg path, find the most likely .tla spec it belongs to.
 * MC-prefixed configs map back to the unprefixed spec if it exists.
 */
/**
 * If the URI points to an MC-prefixed .tla file, resolve to the
 * underlying spec (e.g. MCSpec.tla → Spec.tla).
 */
function resolveSpecUri(fileUri: vscode.Uri): vscode.Uri {
    const filePath = fileUri.fsPath;
    const dir = path.dirname(filePath);
    const baseName = path.basename(filePath, '.tla');

    if (baseName.startsWith('MC') && baseName.length > 2) {
        const unprefixed = baseName.substring(2);
        const candidate = path.join(dir, `${unprefixed}.tla`);
        if (fs.existsSync(candidate)) {
            return vscode.Uri.file(candidate);
        }
    }

    return fileUri;
}

function resolveSpecPathFromCfg(cfgPath: string): string {
    const dir = path.dirname(cfgPath);
    const baseName = path.basename(cfgPath, '.cfg');

    if (baseName.startsWith('MC') && baseName.length > 2) {
        const unprefixed = baseName.substring(2);
        const candidate = path.join(dir, `${unprefixed}.tla`);
        if (fs.existsSync(candidate)) {
            return candidate;
        }
    }

    return replaceExtension(cfgPath, 'tla');
}

function getWebviewHtml(
    webview: vscode.Webview,
    extensionUri: vscode.Uri
): string {
    const scriptUri = getUri(
        webview, extensionUri, ['out', 'model-editor.js']
    );
    const nonce = getNonce();

    return /*html*/ `
    <!DOCTYPE html>
    <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport"
                content="width=device-width, initial-scale=1.0">
            <meta http-equiv="Content-Security-Policy"
                content="default-src 'none';
                    style-src 'unsafe-inline';
                    script-src 'nonce-${nonce}';">
            <title>TLA+ Model Editor</title>
            <style>body { padding: 0 !important; overflow-y: scroll; }</style>
        </head>
        <body>
            <div id="root"></div>
            <script type="module" nonce="${nonce}"
                src="${scriptUri}"></script>
        </body>
    </html>
    `;
}


class ModelEditorPanel {
    private static currentPanel: ModelEditorPanel | undefined;

    private readonly panel: vscode.WebviewPanel;
    private readonly disposables: vscode.Disposable[] = [];
    private specPath: string;

    private constructor(
        extContext: vscode.ExtensionContext, specUri: vscode.Uri
    ) {
        this.specPath = specUri.fsPath;
        const extensionUri = extContext.extensionUri;

        this.panel = vscode.window.createWebviewPanel(
            'tlaplusModelEditor',
            'TLA+ Model Editor',
            { viewColumn: vscode.ViewColumn.Beside, preserveFocus: false },
            {
                enableScripts: true,
                retainContextWhenHidden: true,
                localResourceRoots: [
                    vscode.Uri.joinPath(extensionUri, 'out')
                ]
            }
        );

        this.panel.iconPath = {
            dark: vscode.Uri.joinPath(
                extensionUri, 'resources', 'images', 'preview-dark.svg'
            ),
            light: vscode.Uri.joinPath(
                extensionUri, 'resources', 'images', 'preview-light.svg'
            ),
        };

        this.panel.onDidDispose(
            () => this.dispose(), null, this.disposables
        );

        const setup = setupModelEditorWebview(
            this.panel, extContext, () => this.specPath
        );
        this.disposables.push(...setup.disposables);
        this.sendInit = setup.sendInitData;
    }

    private sendInit: () => Promise<void> = () => Promise.resolve();

    public static createOrReveal(
        extContext: vscode.ExtensionContext, specUri: vscode.Uri
    ): void {
        if (ModelEditorPanel.currentPanel) {
            ModelEditorPanel.currentPanel.specPath = specUri.fsPath;
            ModelEditorPanel.currentPanel.panel.reveal(undefined, false);
            void ModelEditorPanel.currentPanel.sendInit();
            return;
        }
        ModelEditorPanel.currentPanel = new ModelEditorPanel(
            extContext, specUri
        );
    }

    private dispose(): void {
        ModelEditorPanel.currentPanel = undefined;
        this.panel.dispose();
        while (this.disposables.length) {
            const d = this.disposables.pop();
            if (d) { d.dispose(); }
        }
    }
}