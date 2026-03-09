import * as vscode from 'vscode';
import { DCollection, applyDCollection } from '../diagnostic';

export class DiagnosticsProjector {
    constructor(readonly diagnosticCollection: vscode.DiagnosticCollection) {}

    project(diagnostics: DCollection | undefined): void {
        if (!diagnostics) {
            return;
        }
        applyDCollection(diagnostics, this.diagnosticCollection);
    }

    delete(uri: vscode.Uri): void {
        this.diagnosticCollection.delete(uri);
    }
}
