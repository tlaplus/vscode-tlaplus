import * as vscode from 'vscode';
import { CoverageViewPanel } from '../panels/coverageView';

export const CMD_VISUALIZE_COVERAGE = 'tlaplus.coverage.visualize';

export async function visualizeCoverage(uri?: vscode.Uri, extContext?: vscode.ExtensionContext): Promise<void> {
    if (!extContext) {
        vscode.window.showErrorMessage('Extension context not available');
        return;
    }

    // If no URI provided, try to get from active editor
    if (!uri) {
        const activeEditor = vscode.window.activeTextEditor;
        if (activeEditor && activeEditor.document.fileName.endsWith('.ndjson')) {
            uri = activeEditor.document.uri;
        } else {
            // Show file picker
            const fileUris = await vscode.window.showOpenDialog({
                canSelectFiles: true,
                canSelectFolders: false,
                canSelectMany: false,
                filters: {
                    'NDJSON files': ['ndjson']
                },
                title: 'Select simulation coverage file'
            });

            if (!fileUris || fileUris.length === 0) {
                return;
            }
            uri = fileUris[0];
        }
    }

    CoverageViewPanel.render(extContext.extensionUri, uri);
}