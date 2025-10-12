import * as path from 'path';
import * as vscode from 'vscode';
import { moduleSearchPaths } from '../paths';

export async function resolveModuleUri(
    moduleName: string,
    currentDocumentUri: vscode.Uri
): Promise<vscode.Uri | undefined> {
    const moduleFileName = `${moduleName}.tla`;

    const localCandidate = vscode.Uri.file(
        path.join(path.dirname(currentDocumentUri.fsPath), moduleFileName)
    );
    if (await exists(localCandidate)) {
        return localCandidate;
    }

    const workspaceCandidate = await findInWorkspace(moduleFileName, currentDocumentUri);
    if (workspaceCandidate) {
        return workspaceCandidate;
    }

    const searchPathCandidate = await findInSearchPaths(moduleFileName, currentDocumentUri);
    if (searchPathCandidate) {
        return searchPathCandidate;
    }

    return undefined;
}

async function exists(uri: vscode.Uri): Promise<boolean> {
    try {
        await vscode.workspace.fs.stat(uri);
        return true;
    } catch {
        return false;
    }
}

async function findInWorkspace(
    moduleFileName: string,
    currentDocumentUri: vscode.Uri
): Promise<vscode.Uri | undefined> {
    const searchPatterns = [
        `**/${moduleFileName}`,
        `**/modules/${moduleFileName}`,
        `**/specs/${moduleFileName}`,
        `**/src/${moduleFileName}`,
        `**/lib/${moduleFileName}`
    ];

    for (const pattern of searchPatterns) {
        const found = await vscode.workspace.findFiles(pattern, undefined, 1);
        if (found.length > 0) {
            return found[0];
        }
    }
    return undefined;
}

async function findInSearchPaths(
    moduleFileName: string,
    currentDocumentUri: vscode.Uri
): Promise<vscode.Uri | undefined> {
    const sources = moduleSearchPaths.getSources();
    for (const source of sources) {
        const basePaths = moduleSearchPaths.getSourcePaths(source.name) ?? [];
        for (const basePath of basePaths) {
            const resolved = await resolveWithinBasePath(basePath, moduleFileName, currentDocumentUri);
            if (resolved) {
                return resolved;
            }
        }
    }
    return undefined;
}

async function resolveWithinBasePath(
    basePath: string,
    moduleFileName: string,
    currentDocumentUri: vscode.Uri
): Promise<vscode.Uri | undefined> {
    if (!basePath) {
        return undefined;
    }

    if (basePath.startsWith('jar:file:') || basePath.startsWith('jarfile:')) {
        return resolveJarEntry(basePath, moduleFileName);
    }

    const workspaceFolder = vscode.workspace.getWorkspaceFolder(currentDocumentUri);
    const baseDir = workspaceFolder
        ? workspaceFolder.uri.fsPath
        : path.dirname(currentDocumentUri.fsPath);

    const modulePath = path.isAbsolute(basePath)
        ? path.join(basePath, moduleFileName)
        : path.join(baseDir, basePath, moduleFileName);
    const candidate = vscode.Uri.file(modulePath);
    if (await exists(candidate)) {
        return candidate;
    }
    return undefined;
}

async function resolveJarEntry(basePath: string, moduleFileName: string): Promise<vscode.Uri | undefined> {
    const exclamationIndex = basePath.indexOf('!');
    if (exclamationIndex < 0) {
        return undefined;
    }

    const innerPath = basePath.substring(exclamationIndex + 1);
    const normalizedInner = innerPath.startsWith('/') ? innerPath : `/${innerPath}`;
    const moduleInnerPath = path.posix.join(normalizedInner.replace(/^\//, ''), moduleFileName);

    let jarFsPath: string | undefined;
    if (basePath.startsWith('jar:file:')) {
        const jarPrefix = basePath.substring(0, exclamationIndex);
        const jarFileUri = vscode.Uri.parse(jarPrefix.replace(/^jar:/, ''));
        jarFsPath = jarFileUri.fsPath;
    } else {
        const rawPath = basePath.substring('jarfile:'.length, exclamationIndex);
        try {
            jarFsPath = vscode.Uri.file(rawPath).fsPath;
        } catch {
            jarFsPath = rawPath;
        }
    }

    if (!jarFsPath) {
        return undefined;
    }

    const jarUri = createJarUri(jarFsPath, moduleInnerPath);
    if (await exists(jarUri)) {
        return jarUri;
    }
    return undefined;
}

function createJarUri(archivePath: string, internalPath: string): vscode.Uri {
    const normalizedInternal = internalPath.startsWith('/') ? internalPath : `/${internalPath}`;
    return vscode.Uri.parse(`jarfile:${archivePath}!${normalizedInternal}`);
}
