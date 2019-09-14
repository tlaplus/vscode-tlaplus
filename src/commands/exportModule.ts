import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';
import { LANG_TLAPLUS, replaceExtension } from '../common';
import { runTex } from '../tla2tools';
import { ToolOutputChannel } from '../outputChannels';

export const CMD_EXPORT_TLA_TO_TEX = 'tlaplus.exportToTex';
const NO_ERROR = 0;

let outChannel: ToolOutputChannel | undefined;

/**
 * Runs tla2tex tool on the currently open TLA+ module.
 */
export async function exportModuleToTex(extContext: vscode.ExtensionContext) {
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
        vscode.window.showWarningMessage('No editor is active, cannot export a TLA+ module to TeX');
        return;
    }
    if (editor.document.languageId !== LANG_TLAPLUS) {
        vscode.window.showWarningMessage('File in the active editor is not a TLA+ file, it cannot be exported to TeX');
        return;
    }
    generateTexFile(editor.document.uri.fsPath, true);
}

async function generateTexFile(tlaFilePath: string, notifySuccess: boolean) {
    const procInfo = await runTex(tlaFilePath);
    getOutChannel().bindTo(procInfo);
    procInfo.process.on('close', (exitCode) => {
        if (exitCode !== NO_ERROR) {
            getOutChannel().revealWindow();
            return;
        }
        const fileName = path.basename(tlaFilePath);
        const texName = replaceExtension(fileName, 'tex');
        const dviName = replaceExtension(fileName, 'dvi');
        removeTempFiles(tlaFilePath);
        if (notifySuccess) {
            vscode.window.showInformationMessage(`${texName} and ${dviName} generated.`);
        }
    });
}

async function removeTempFiles(tlaFilePath: string) {
    await removeFile(replaceExtension(tlaFilePath, 'log'));
    await removeFile(replaceExtension(tlaFilePath, 'aux'));
}

function removeFile(filePath: string): Promise<void> {
    return new Promise((resolve, reject) => {
        fs.unlink(filePath, () => resolve());
    });
}

function getOutChannel(): ToolOutputChannel {
    if (!outChannel) {
        outChannel = new ToolOutputChannel('TLA+ to TeX');
    }
    return outChannel;
}
