import * as path from 'path';
import * as vscode from 'vscode';
import { listFiles } from '../common';
import {
    doCheckModel, getSpecFiles, stopModelChecking
} from '../commands/checkModel';
import { SpecFiles } from '../model/check';

export const TLAPLUS_DEBUG_LAUNCH_SMOKE = 'tlaplus.debugger.smoke';
export const TLAPLUS_DEBUG_LAUNCH_CHECKNDEBUG = 'tlaplus.debugger.run';
export const TLAPLUS_DEBUG_LAUNCH_CUSTOMCHECKNDEBUG = 'tlaplus.debugger.customRun';
export const TLAPLUS_DEBUG_LAUNCH_DEBUG = 'tlaplus.debugger.attach';

const DEFAULT_DEBUGGER_PORT = 4712;
const DEBUGGER_MIN_PORT = 5001;         // BSD uses ports up to 5000 as ephemeral
const DEBUGGER_MAX_PORT = 49151;        // Ports above 49152 are suggested as ephemeral by IANA

export class TLADebugAdapterServerDescriptorFactory implements vscode.DebugAdapterDescriptorFactory {

    createDebugAdapterDescriptor(session: vscode.DebugSession, executable: vscode.DebugAdapterExecutable | undefined):
        vscode.ProviderResult<vscode.DebugAdapterDescriptor> {
        return new vscode.DebugAdapterServer(session.configuration['port']);
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
    // Accept .tla files here because TLC configs and TLA+ modules can share the same file:
    // https://github.com/alygin/vscode-tlaplus/issues/220
    const configFiles = await listFiles(path.dirname(targetResource.fsPath),
        (fName) => fName.endsWith('.cfg') || fName.endsWith('.tla'));
    configFiles.sort();
    const cfgFileName = await vscode.window.showQuickPick(
        configFiles,
        { canPickMany: false, placeHolder: 'Select a model config file', matchOnDetail: true }
    );
    if (!cfgFileName || cfgFileName.length === 0) {
        return;
    }
    const specFiles = new SpecFiles(
        targetResource.fsPath,
        path.join(path.dirname(targetResource.fsPath), cfgFileName)
    );
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
    const specFiles = await getSpecFiles(targetResource, prefixPath + prefixName);
    if (!specFiles || !specFiles.cfgFileName.startsWith(prefixName)) {
        // Launch the debugger iff there is a Smoke model. specFiles
        // might be an ordinary model, which we don't want to run in TLC
        // automatically.
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
