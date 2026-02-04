import * as path from 'path';
import * as vscode from 'vscode';
import { exists, replaceExtension } from '../common';
import {
    doCheckModel, getSpecFiles, stopModelChecking
} from '../commands/checkModel';
import { SpecFiles } from '../model/check';
import { extractFingerprintFromTrace, findLatestTraceFile } from '../tla2tools';

export const TLAPLUS_DEBUG_LAUNCH_SMOKE = 'tlaplus.debugger.smoke';
export const TLAPLUS_DEBUG_LAUNCH_CHECKNDEBUG = 'tlaplus.debugger.run';
export const TLAPLUS_DEBUG_LAUNCH_CUSTOMCHECKNDEBUG = 'tlaplus.debugger.customRun';
export const TLAPLUS_DEBUG_LAUNCH_DEBUG = 'tlaplus.debugger.attach';
export const TLAPLUS_DEBUG_GOTO_STATE = 'tlaplus.debugger.gotoState';
export const TLAPLUS_DEBUG_LOAD_TRACE = 'tlaplus.debugger.loadTrace';

const DEFAULT_DEBUGGER_PORT = 4712;
const DEBUGGER_MIN_PORT = 5001;         // BSD uses ports up to 5000 as ephemeral
const DEBUGGER_MAX_PORT = 49151;        // Ports above 49152 are suggested as ephemeral by IANA
const CTX_DEBUGGER_SUPPORTS_GOTO_STATE = 'tlaplus.debugger.supportsGotoState';

export class TLADebugAdapterServerDescriptorFactory implements vscode.DebugAdapterDescriptorFactory {

    createDebugAdapterDescriptor(session: vscode.DebugSession, executable: vscode.DebugAdapterExecutable | undefined):
        vscode.ProviderResult<vscode.DebugAdapterDescriptor> {
        return new vscode.DebugAdapterServer(session.configuration['port']);
    }
}

/**
 * Tracks debug adapter protocol messages to detect capabilities from the debugger backend.
 */
export class TLADebugAdapterTrackerFactory implements vscode.DebugAdapterTrackerFactory {

    createDebugAdapterTracker(session: vscode.DebugSession): vscode.ProviderResult<vscode.DebugAdapterTracker> {
        if (session.type !== 'tlaplus') {
            return;
        }

        return {
            onDidSendMessage: (message: unknown) => {
                // Listen for the initialize response from the debug adapter
                if (this.isInitializeResponse(message)) {
                    const supportsGotoState = message.body?.supportsGotoState === true;
                    vscode.commands.executeCommand('setContext', CTX_DEBUGGER_SUPPORTS_GOTO_STATE, supportsGotoState);
                }
            },
            onWillStopSession: () => {
                // Clear the context when the debug session ends
                vscode.commands.executeCommand('setContext', CTX_DEBUGGER_SUPPORTS_GOTO_STATE, false);
            }
        };
    }

    private isInitializeResponse(message: unknown): message is { type: string; command: string; body?: { supportsGotoState?: boolean } } {
        return typeof message === 'object' &&
               message !== null &&
               'type' in message &&
               typeof (message as any).type === 'string' &&
               (message as any).type === 'response' &&
               'command' in message &&
               typeof (message as any).command === 'string' &&
               (message as any).command === 'initialize';
    }
}

/**
 * Attaches the DAP front-end to an already running TLC debugger.
 */
export async function attachDebugger(): Promise<void> {
    // Attaching to a separately launched TLC leaves the result view (webview) empty.
    // However, TLC sends its output via the DAP Output event
    // (https://microsoft.github.io/debug-adapter-protocol/specification#Events_Output)
    // to VSCode. If needed, this output can be captured by a DebugAdapterTracker
    // (see debug.registerDebugAdapterTrackerFactory()).
    vscode.debug.startDebugging(undefined, {
        type: 'tlaplus',
        name: 'Debug Spec',
        request: 'launch',
        port: DEFAULT_DEBUGGER_PORT
    });
}

/**
 * Runs TLC in debugger mode and attaches the DAP front-end.
 */
export async function checkAndDebugSpec(
    resource: vscode.Uri | undefined,
    diagnostic: vscode.DiagnosticCollection,
    context: vscode.ExtensionContext
): Promise<void> {
    let targetResource = resource;
    if (!targetResource && vscode.window.activeTextEditor) {
        // Since this command is registered as a button on the editor menu, I don't
        // think this branch is ever taken.  It's here because the DAP example has it.
        targetResource = vscode.window.activeTextEditor.document.uri;
    }
    if (!targetResource) {
        return;
    }
    const specFiles = await getSpecFiles(targetResource);
    if (!specFiles) {
        return;
    }
    // Randomly select a port on which we request the debugger to listen
    const initPort = Math.floor(Math.random() * (DEBUGGER_MAX_PORT - DEBUGGER_MIN_PORT)) + DEBUGGER_MIN_PORT; //NOSONAR
    // This will be called as soon as TLC starts listening on a port or fails to start
    const portOpenCallback = (port?: number) => {
        if (!port) {
            return;
        }
        vscode.debug.startDebugging(undefined, {
            type: 'tlaplus',
            name: 'Debug Spec',
            request: 'launch',
            port: port
        });
    };
    // Don't await doCheckModel because it only returns after TLC terminates.
    doCheckModel(specFiles, false, context, diagnostic, true, ['-debugger', `port=${initPort}`], portOpenCallback);
}

export async function checkAndDebugSpecCustom(
    resource: vscode.Uri | undefined,
    diagnostic: vscode.DiagnosticCollection,
    context: vscode.ExtensionContext
): Promise<void> {
    let targetResource = resource;
    if (!targetResource && vscode.window.activeTextEditor) {
        // Since this command is registered as a button on the editor menu, I don't
        // think this branch is ever taken.  It's here because the DAP example has it.
        targetResource = vscode.window.activeTextEditor.document.uri;
    }
    if (!targetResource) {
        return;
    }
    const specFiles = await getSpecFiles(targetResource, true, true, 'customPick');
    if (!specFiles) {
        return;
    }
    // Randomly select a port on which we request the debugger to listen
    const initPort = Math.floor(Math.random() * (DEBUGGER_MAX_PORT - DEBUGGER_MIN_PORT)) + DEBUGGER_MIN_PORT; //NOSONAR
    // This will be called as soon as TLC starts listening on a port or fails to start
    const portOpenCallback = (port?: number) => {
        if (!port) {
            return;
        }
        vscode.debug.startDebugging(undefined, {
            type: 'tlaplus',
            name: 'Debug Spec',
            request: 'launch',
            port: port
        });
    };
    // Don't await doCheckModel because it only returns after TLC terminates.
    doCheckModel(specFiles, false, context, diagnostic, true, ['-debugger', `port=${initPort}`], portOpenCallback);
}

export async function smokeTestSpec(
    resource: vscode.Uri | undefined,
    diagnostic: vscode.DiagnosticCollection,
    context: vscode.ExtensionContext
): Promise<void> {
    let targetResource = resource;
    if (!targetResource && vscode.window.activeTextEditor) {
        // Since this command is registered as a button on the editor menu, I don't
        // think this branch is ever taken.  It's here because the DAP example has it.
        targetResource = vscode.window.activeTextEditor.document.uri;
    }
    if (!targetResource) {
        return;
    }

    const prefixPath = vscode.workspace.getConfiguration().get<string>('tlaplus.smoke.prefix.path', '');
    const prefixName = vscode.workspace.getConfiguration().get<string>('tlaplus.smoke.prefix.name', 'Smoke');
    const baseName = path.basename(targetResource.fsPath);
    const smokePrefix = `${prefixPath}${prefixName}`;
    const smokeTlaPath = path.join(path.dirname(targetResource.fsPath), `${smokePrefix}${baseName}`);
    const smokeCfgPath = replaceExtension(smokeTlaPath, 'cfg');
    const smokeTlaExists = await exists(smokeTlaPath);
    const smokeCfgExists = await exists(smokeCfgPath);
    if (!smokeTlaExists || !smokeCfgExists) {
        return;
    }
    const specFiles = new SpecFiles(smokeTlaPath, smokeCfgPath);
    // Randomly select a port on which we request the debugger to listen
    const initPort = Math.floor(Math.random() * (DEBUGGER_MAX_PORT - DEBUGGER_MIN_PORT)) + DEBUGGER_MIN_PORT; //NOSONAR
    // This will be called as soon as TLC starts listening on a port or fails to start
    const portOpenCallback = (port?: number) => {
        if (!port) {
            return;
        }
        vscode.debug.startDebugging(undefined, {
            type: 'tlaplus',
            name: 'Debug Spec',
            request: 'launch',
            port: port
        });
    };

    // Terminate another model-checking run if any, but do *not* terminate a
    // manually/explicitly started TLC process.
    const terminateLastRun = (lastSpecFiles: SpecFiles | undefined): boolean => {
        if (!lastSpecFiles) {
            return false;
        }
        return lastSpecFiles.cfgFileName.startsWith(prefixName);
    };
    stopModelChecking(terminateLastRun, true);

    // Don't await doCheckModel because it only returns after TLC terminates.
    doCheckModel(specFiles, false, context, diagnostic, false,
        ['-simulate', '-noTE', '-debugger', `nosuspend,port=${initPort}`], portOpenCallback);
}

/**
 * Context passed to commands invoked from the debug/variables/context menu.
 */
interface DebugVariableContext {
    container: {
        name: string;
        value: string;
        variablesReference: number;
    };
    variable: {
        name: string;
        value: string;
        variablesReference: number;
        evaluateName?: string;
    };
}

/**
 * Goes to a specific state in the TLA+ debugger by sending a custom DAP request.
 * This command is triggered from the variables view context menu or keyboard shortcut.
 *
 * @param context The debug variable context from the variables view (may be undefined if triggered via keyboard)
 */
export async function gotoState(context: DebugVariableContext | undefined): Promise<void> {
    // Context is undefined when triggered via keyboard shortcut without a selection
    if (!context?.variable) {
        vscode.window.showInformationMessage('Please select a state in the variables view.');
        return;
    }

    const session = vscode.debug.activeDebugSession;
    if (!session) {
        vscode.window.showWarningMessage('No active debug session');
        return;
    }

    if (session.type !== 'tlaplus') {
        vscode.window.showWarningMessage('This command is only available for TLA+ debug sessions');
        return;
    }

    const variable = context.variable;

    try {
        // Send a custom DAP request to the TLC debugger
        // The 'tlaplus/gotoState' request is a custom extension to the DAP protocol
        // Arguments wrapped in object for JSON-RPC named parameter binding (LSP4J)
        await session.customRequest('tlaplus/gotoState', { variablesReference: variable.variablesReference });
    } catch (error) {
        const errorMessage = error instanceof Error ? error.message : String(error);
        vscode.window.showErrorMessage(`Failed to go to state: ${errorMessage}`);
    }
}

/**
 * Debugs a counterexample by loading the most recent trace file.
 * The trace file is loaded using TLC's -loadtrace option with the appropriate -fp index.
 * This allows stepping through the exact execution that was previously captured.
 *
 * @param tlaFilePath Path to the TLA+ specification file (optional, will use active editor if not provided)
 * @param diagnostic Diagnostic collection for error reporting
 * @param context Extension context
 */
export async function debugCounterexample(
    tlaFilePath: string | undefined,
    diagnostic: vscode.DiagnosticCollection,
    context: vscode.ExtensionContext
): Promise<void> {
    // If no path provided, try to get it from the active editor
    let targetTlaFilePath = tlaFilePath;
    if (!targetTlaFilePath) {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showWarningMessage('No TLA+ file specified and no active editor found');
            return;
        }
        targetTlaFilePath = editor.document.uri.fsPath;
    }

    // Get the spec files
    const specFiles = await getSpecFiles(vscode.Uri.file(targetTlaFilePath), false, true);
    if (!specFiles) {
        vscode.window.showWarningMessage('Could not determine specification files');
        return;
    }

    // Find the latest trace file
    const traceFilePath = await findLatestTraceFile(specFiles.tlaFilePath, specFiles.cfgFilePath);
    if (!traceFilePath) {
        vscode.window.showWarningMessage(
            'No trace file found. Run model checking in BFS mode to generate a trace file.'
        );
        return;
    }

    // Extract the fingerprint from the trace filename
    const fpValue = extractFingerprintFromTrace(traceFilePath);
    if (fpValue === undefined) {
        vscode.window.showErrorMessage(
            `Could not extract fingerprint index from trace file: ${path.basename(traceFilePath)}`
        );
        return;
    }

    // Randomly select a port for the debugger
    const initPort = Math.floor(Math.random() * (DEBUGGER_MAX_PORT - DEBUGGER_MIN_PORT)) + DEBUGGER_MIN_PORT; //NOSONAR

    // Callback when the debugger port is opened
    const portOpenCallback = (port?: number) => {
        if (!port) {
            return;
        }
        vscode.debug.startDebugging(undefined, {
            type: 'tlaplus',
            name: 'Debug Trace',
            request: 'launch',
            port: port
        });
    };

    // Build the TLC options with -loadtrace (format first, then file path)
    const debugOptions = [
        '-fp', String(fpValue),
        '-loadtrace', 'tlc', traceFilePath,
        '-debugger', `port=${initPort}`
    ];

    // Don't await doCheckModel because it only returns after TLC terminates
    doCheckModel(specFiles, false, context, diagnostic, false, debugOptions, portOpenCallback);
}
