/**
 * sequenceDiagramView.ts — Generate PlantUML from TLC traces.
 *
 * The extension generates PlantUML text from TLC output — it does NOT render
 * SVG.  Users who want a visual preview install a dedicated PlantUML extension
 * (e.g. jebbs.plantuml) which handles rendering, export, and live preview.
 *
 * Public API:
 *  - showSequenceDiagramFromPuml() Open generated PlantUML text in a new editor.
 *  - showSequenceDiagram()         Convert TraceData → PlantUML → new editor.
 */
import * as vscode from 'vscode';
import { TraceData } from '../webview/sequenceDiagram/types';
import { traceDataToPlantUml } from '../generators/plantUmlGenerator';

/**
 * Show generated PlantUML text in a new untitled editor tab.
 * Users can save the file or use a PlantUML extension to preview it.
 */
export async function showSequenceDiagramFromPuml(
    puml: string,
    _extContext: vscode.ExtensionContext,
    _title?: string,
): Promise<void> {
    const doc = await vscode.workspace.openTextDocument({
        content: puml,
        language: 'plantuml',
    });
    await vscode.window.showTextDocument(doc, {
        viewColumn: vscode.ViewColumn.Beside,
        preserveFocus: true,
        preview: false,
    });
}

/**
 * Convert structured TraceData to PlantUML and open in a new editor.
 */
export async function showSequenceDiagram(
    data: TraceData,
    extContext: vscode.ExtensionContext,
): Promise<void> {
    const puml = traceDataToPlantUml(data);
    await showSequenceDiagramFromPuml(puml, extContext);
}
