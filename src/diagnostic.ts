import * as vscode from 'vscode';
import { pathToModuleName, pathToUri } from './common';

/**
 * Collection of DMessages that were generated during a single check run.
 */
export class DCollection {
    private readonly modules: Map<string, string> = new Map();   // Map of checked modules names to file paths
    private readonly messages: DMessage[] = [];                  // Collection of diagnostic messages from the check run

    public getModules(): ReadonlyMap<string, string> {
        return this.modules;
    }

    public getMessages(): ReadonlyArray<DMessage> {
        return this.messages;
    }

    public addFilePath(filePath: string): void {
        this.modules.set(pathToModuleName(filePath), filePath);
    }

    public addMessage(
        filePath: string,
        range: vscode.Range,
        text: string,
        severity = vscode.DiagnosticSeverity.Error
    ): void {
        this.messages.push(new DMessage(filePath, range, text, severity));
        this.addFilePath(filePath);
    }

    public addAll(src: DCollection): void {
        src.messages.forEach((msg) => this.messages.push(msg));
        src.modules.forEach((path, mod) => this.modules.set(mod, path));
    }
}

/**
 * Applies all the messages from the given collection.
 * Also removes messages from the checked files if necessary.
 */
export function applyDCollection(dCol: DCollection, dc: vscode.DiagnosticCollection): void {
    // Clear diagnostic for all checked files
    dCol.getModules().forEach((modPath) => dc.delete(pathToUri(modPath)));
    // Add messages that were found
    const uri2diag = new Map<string, vscode.Diagnostic[]>();
    dCol.getMessages().forEach((d) => {
        let list = uri2diag.get(d.filePath);
        if (!list) {
            list = [];
            uri2diag.set(d.filePath, list);
        }
        list.push(d.diagnostic);
    });
    uri2diag.forEach((diags, path) => dc.set(pathToUri(path), diags));
}

/**
 * Adds all diagnostics from one collection to another.
 */
export function addDiagnostics(from: DCollection, to: DCollection): void {
    from.getModules().forEach((modPath) => to.addFilePath(modPath));
    from.getMessages().forEach((msg) =>
        to.addMessage(msg.filePath, msg.diagnostic.range, msg.diagnostic.message, msg.diagnostic.severity)
    );
}

/**
 * A Diagnostic instance linked to the corresponding file.
 */
class DMessage {
    readonly filePath: string;
    readonly diagnostic: vscode.Diagnostic;

    constructor(
        filePath: string,
        range: vscode.Range,
        text: string,
        severity: vscode.DiagnosticSeverity
    ) {
        this.filePath = filePath;
        this.diagnostic = new vscode.Diagnostic(range, text, severity);
    }
}
