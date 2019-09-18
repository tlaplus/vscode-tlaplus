import * as vscode from 'vscode';
import * as path from 'path';
import { createTempDirSync, listFiles, copyFile } from '../common';

/**
 * Creates custom specification and model config for a specific check run.
 * Such models are treated as temporary, they deleted after checking.
 * @param baseSpec .tla file that must be used as a base specification for the custom model.
 */
export async function createCustomModel(baseSpec: string): Promise<string | undefined> {
    const tempDir = createTempDirSync();
    if (!tempDir) {
        return undefined;
    }
    try {
        await copySpecFiles(path.dirname(baseSpec), tempDir);
        return tempDir;
    } catch (err) {
        console.error(err);
        vscode.window.showErrorMessage(`Cannot copy spec and model files: ${err}`);
    }
    return undefined;
}

async function copySpecFiles(srcDir: string, destDir: string) {
    const fileNames = await listFiles(
        srcDir,
        (fName) => fName.endsWith('.tla') || fName.endsWith('.cfg')
    );
    for (const fName of fileNames) {
        await copyFile(path.join(srcDir, fName), destDir);
    }
}
