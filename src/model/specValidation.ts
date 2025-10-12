import * as fs from 'fs/promises';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { LANG_TLAPLUS } from '../common';
import { SpecFiles } from './check';
import { resolveModuleUri } from './moduleResolver';
import { extractModuleName, extractReferencedModuleNames, fallbackModuleNameFromPath } from './tlaModuleUtils';
import { runSany } from '../tla2tools';
import { SanyData, SanyStdoutParser } from '../parsers/sany';

export interface SpecValidationOptions {
    documentOverrides?: Map<string, string>;
    sanyRunner?: (tlaFilePath: string, libraryDirs: string[]) => Promise<SanyData>;
}

export interface SpecValidationResult {
    success: boolean;
    message?: string;
}

interface ModuleMetadata {
    originalPath: string;
    moduleName: string;
    referencedModules: Set<string>;
    content: string;
}

interface SnapshotInfo {
    rootDir: string;
    pathMap: Map<string, string>;
    libraryDirs: string[];
}

const TEMP_DIR_PREFIX = 'tlaplus-model-snapshot-';

export async function validateModelSpecPair(
    specFiles: SpecFiles,
    activeSpecPath: string,
    options: SpecValidationOptions = {}
): Promise<SpecValidationResult> {
    const normalize = normalizeFsPath;
    const normalizedActiveSpec = normalize(activeSpecPath);
    const normalizedModelPath = normalize(specFiles.tlaFilePath);

    if (normalizedActiveSpec === normalizedModelPath) {
        return { success: true };
    }

    const overrides = options.documentOverrides ?? collectOpenDocumentOverrides();
    const modules = await collectModules(
        new Set<string>([specFiles.tlaFilePath, activeSpecPath]),
        overrides
    );

    const activeSpecMetadata = modules.get(normalizedActiveSpec);
    if (!activeSpecMetadata) {
        return {
            success: false,
            message: `Cannot read active specification module at ${activeSpecPath}.`
        };
    }

    const snapshot = await createSnapshot(modules);
    try {
        const sany = await runSanyWithSnapshot(
            snapshot,
            normalizedModelPath,
            options.sanyRunner
        );
        const success = verifySpecReferenced(
            sany,
            activeSpecMetadata,
            snapshot,
            normalizedActiveSpec
        );
        if (success.success) {
            return success;
        }
        return {
            success: false,
            message: success.message
        };
    } catch (err) {
        const message = err instanceof Error ? err.message : String(err);
        return {
            success: false,
            message: `Unable to validate model against active specification: ${message}`
        };
    } finally {
        await removeSnapshot(snapshot);
    }
}

function collectOpenDocumentOverrides(): Map<string, string> {
    const normalize = normalizeFsPath;
    const overrides = new Map<string, string>();
    vscode.workspace.textDocuments
        .filter(doc => doc.languageId === LANG_TLAPLUS)
        .forEach(doc => overrides.set(normalize(doc.uri.fsPath), doc.getText()));
    return overrides;
}

async function collectModules(
    rootPaths: Set<string>,
    overrides: Map<string, string>
): Promise<Map<string, ModuleMetadata>> {
    const modules = new Map<string, ModuleMetadata>();
    const queue: string[] = Array.from(rootPaths);

    while (queue.length > 0) {
        const currentPath = queue.pop();
        if (!currentPath) {
            continue;
        }
        const normalized = normalizeFsPath(currentPath);
        if (modules.has(normalized)) {
            continue;
        }
        const canonicalPath = path.resolve(currentPath);
        const content = await getModuleContent(canonicalPath, overrides);
        const moduleName = extractModuleName(content) ?? fallbackModuleNameFromPath(canonicalPath);
        const references = extractReferencedModuleNames(content);
        modules.set(normalized, {
            originalPath: canonicalPath,
            moduleName,
            referencedModules: references,
            content
        });

        for (const referencedName of references) {
            const resolved = await resolveModuleUri(referencedName, vscode.Uri.file(canonicalPath));
            if (resolved && resolved.scheme === 'file') {
                queue.push(resolved.fsPath);
            }
        }
    }
    return modules;
}

async function getModuleContent(fsPath: string, overrides: Map<string, string>): Promise<string> {
    const normalized = normalizeFsPath(fsPath);
    const fromOverride = overrides.get(normalized);
    if (typeof fromOverride === 'string') {
        return fromOverride;
    }
    try {
        return await fs.readFile(fsPath, 'utf8');
    } catch (err) {
        throw new Error(`Cannot read module ${fsPath}: ${err instanceof Error ? err.message : String(err)}`);
    }
}

async function createSnapshot(modules: Map<string, ModuleMetadata>): Promise<SnapshotInfo> {
    const rootDir = await fs.mkdtemp(path.join(os.tmpdir(), TEMP_DIR_PREFIX));
    const pathMap = new Map<string, string>();
    const libraryDirs = new Set<string>();

    for (const [normalizedPath, metadata] of modules.entries()) {
        const relative = deriveSnapshotRelativePath(metadata.originalPath);
        const targetPath = path.join(rootDir, relative);
        await fs.mkdir(path.dirname(targetPath), { recursive: true });
        await fs.writeFile(targetPath, metadata.content, 'utf8');
        pathMap.set(normalizedPath, targetPath);
        libraryDirs.add(path.dirname(targetPath));
    }

    return {
        rootDir,
        pathMap,
        libraryDirs: Array.from(libraryDirs)
    };
}

async function removeSnapshot(snapshot: SnapshotInfo): Promise<void> {
    try {
        await fs.rm(snapshot.rootDir, { recursive: true, force: true });
    } catch {
        // Best-effort cleanup
    }
}

async function runSanyWithSnapshot(
    snapshot: SnapshotInfo,
    normalizedModelPath: string,
    sanyRunner?: (tlaFilePath: string, libraryDirs: string[]) => Promise<SanyData>
): Promise<SanyData> {
    const modelSnapshotPath = snapshot.pathMap.get(normalizedModelPath);
    if (!modelSnapshotPath) {
        throw new Error('Snapshot missing model module.');
    }

    const runner = sanyRunner ?? defaultSanyRunner;
    return runner(modelSnapshotPath, snapshot.libraryDirs);
}

async function defaultSanyRunner(tlaFilePath: string, libraryDirs: string[]): Promise<SanyData> {
    const procInfo = await runSany(tlaFilePath, { extraLibraryPaths: libraryDirs });
    const parser = new SanyStdoutParser(procInfo.process.stdout);
    return parser.readAll();
}

function verifySpecReferenced(
    sany: SanyData,
    specMetadata: ModuleMetadata,
    snapshot: SnapshotInfo,
    normalizedActiveSpec: string
): SpecValidationResult {
    const expectedSnapshotPath = snapshot.pathMap.get(normalizedActiveSpec);
    if (!expectedSnapshotPath) {
        return {
            success: false,
            message: `Snapshot missing expected specification module ${specMetadata.moduleName}.`
        };
    }

    const referencedPath = sany.modulePaths.get(specMetadata.moduleName);
    if (!referencedPath) {
        return {
            success: false,
            message: `Model does not EXTEND or INSTANCE module ${specMetadata.moduleName}.`
        };
    }

    if (!pathsEqual(referencedPath, expectedSnapshotPath)) {
        return {
            success: false,
            message: `Model references ${specMetadata.moduleName} at ${referencedPath}, `
                + `not the active module at ${specMetadata.originalPath}.`
        };
    }

    return { success: true };
}

function deriveSnapshotRelativePath(originalPath: string): string {
    const workspaceFolders = vscode.workspace.workspaceFolders ?? [];
    for (const folder of workspaceFolders) {
        const relative = path.relative(folder.uri.fsPath, originalPath);
        if (!relative.startsWith('..') && !path.isAbsolute(relative)) {
            return path.join(folder.name, relative);
        }
    }
    return path.join('external', sanitizeExternalPath(originalPath));
}

function sanitizeExternalPath(fsPath: string): string {
    const withoutDrive = fsPath.replace(/:/g, '');
    const normalized = withoutDrive.replace(/\\/g, '/');
    const parts = normalized.split('/').filter(Boolean);
    if (parts.length === 0) {
        return path.basename(fsPath);
    }
    return path.join(...parts);
}

function normalizeFsPath(fsPath: string): string {
    const resolved = path.resolve(fsPath);
    return process.platform === 'win32' ? resolved.toLowerCase() : resolved;
}

function pathsEqual(pathA: string, pathB: string): boolean {
    const normalize = (p: string) => {
        const resolved = path.resolve(p);
        return process.platform === 'win32' ? resolved.toLowerCase() : resolved;
    };
    return normalize(pathA) === normalize(pathB);
}
