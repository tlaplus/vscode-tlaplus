/**
 * sequenceDiagramView.ts — Open PlantUML text in a VS Code editor.
 *
 * The extension generates PlantUML text from TLC output — it does NOT render
 * SVG.  Users who want a visual preview install a dedicated PlantUML extension
 * (e.g. jebbs.plantuml) which handles rendering, export, and live preview.
 */
import * as vscode from 'vscode';

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
