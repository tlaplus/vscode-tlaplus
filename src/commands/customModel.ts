import * as vscode from 'vscode';
import * as path from 'path';
import { createTempDirSync, listFiles, copyFile, writeFile } from '../common';

export class CustomModelInfo {
    constructor(
        readonly dirPath: string,
        readonly tlaFileName: string,
        readonly cfgFileName: string
    ) {}
}

/**
 * Creates custom specification and model config for a specific check run.
 * Such models are treated as temporary, they deleted after checking.
 * @param baseSpec .tla file that must be used as a base specification for the custom model.
 */
export async function createCustomModel(
    baseSpec: string,
    tlaContents: string[],
    cfgContents: string[]
): Promise<CustomModelInfo | undefined> {
    const tempDir = createTempDirSync();
    if (!tempDir) {
        return undefined;
    }
    const copied = await copySpecFiles(path.dirname(baseSpec), tempDir);
    if (!copied) {
        return undefined;
    }
    const rootModule = 't' + (new Date().getTime());
    const baseModuleFile = path.basename(baseSpec);
    const baseModule = baseModuleFile.substring(0, baseModuleFile.length - 4);
    const rootModuleFileName = rootModule + '.tla';
    const tlaCreated = await createFile(
        path.join(tempDir, rootModuleFileName),
        `---- MODULE ${rootModule} ----`,
        `EXTENDS ${baseModule}, TLC`,
        ...tlaContents,
        '===='
    );
    if (!tlaCreated) {
        return undefined;
    }
    const cfgFileName = rootModule + '.cfg';
    const cfgCreated = await createFile(path.join(tempDir, cfgFileName), ...cfgContents);
    if (!cfgCreated) {
        return undefined;
    }
    return new CustomModelInfo(tempDir, rootModuleFileName, cfgFileName);
}

async function copySpecFiles(srcDir: string, destDir: string): Promise<boolean> {
    try {
        const fileNames = await listFiles(srcDir, (fName) => fName.endsWith('.tla'));
        for (const fName of fileNames) {
            await copyFile(path.join(srcDir, fName), destDir);
        }
        return true;
    } catch (err) {
        console.error(err);
        vscode.window.showErrorMessage(`Cannot copy spec and model files: ${err}`);
    }
    return false;
}

async function createFile(filePath: string, ...contents: string[]): Promise<boolean> {
    try {
        await writeFile(filePath, ...contents);
        return true;
    } catch (err) {
        console.error(err);
        vscode.window.showErrorMessage(`Cannot create file ${filePath}: ${err}`);
    }
    return false;
}
