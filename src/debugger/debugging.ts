import * as vscode from 'vscode';
import {
    doCheckModel, getSpecFiles
} from '../commands/checkModel';

export const TLAPLUS_DEBUG_LAUNCH_CHECKNDEBUG = 'tlaplus.debug.checkAndDebugEditorContents';
export const TLAPLUS_DEBUG_LAUNCH_DEBUG = 'tlaplus.debug.debugEditorContents';

export class TLADebugAdapterServerDescriptorFactory implements vscode.DebugAdapterDescriptorFactory {

    createDebugAdapterDescriptor(session: vscode.DebugSession, executable: vscode.DebugAdapterExecutable | undefined):
        vscode.ProviderResult<vscode.DebugAdapterDescriptor> {
        return new vscode.DebugAdapterServer(session.configuration['port']);
    }
}

/**
 * Attaches the DAP front-end to an already running TLC debugger.
 */
export async function debugSpec(
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
    if (targetResource) {
        // Attaching to a separately launched TLC leaves the result view (webview) empty.
        // However, TLC sends its output via the DAP Output event
        // (https://microsoft.github.io/debug-adapter-protocol/specification#Events_Output)
        // to VSCode.  Somebody has to figure out how to wire this up. In the meantime,
        // users have to manually "parse" the output on VSCode's DebugConsole. Unfortunately,
        // it is TLC's '-tool' output containing "@!@!@" markers around each message.
        vscode.debug.startDebugging(undefined, {
            type: 'tlaplus',
            name: 'Debug Spec',
            request: 'launch',
            program: targetResource.fsPath,
            port: '4712'
        });
    }
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
    if (targetResource) {
        const specFiles = await getSpecFiles(targetResource);
        if (!specFiles) {
            return;
        }
        // Randomly select a port on which we request the debugger to listen
        const port = Math.floor(Math.random() * (64510 - 1025 + 1)) + 1025;
        // false => Don't open the result view, it's empty anyway (see above).
        // Don't await doCheckModel because it only returns after TLC terminates.
        doCheckModel(specFiles, false, context, diagnostic, false, ['-debugger', `port=${port}`]);
        setTimeout(function() {
            if (targetResource) {
                vscode.debug.startDebugging(undefined, {
                    type: 'tlaplus',
                    name: 'Debug Spec',
                    request: 'launch',
                    program: targetResource.fsPath,
                    port: port
                });
            }
        }, 5_000); // Wait five seconds hoping this is enough for TLC to start listening.
        // In the future, we have to come up with a non-racy handshake.  What would be
        // way more elegant is for VSCode to a) open a serversocket on a free port, b)
        // launch the TLC process passing the port number, and c) for TLC to connect
        // to the given port.
    }
}
