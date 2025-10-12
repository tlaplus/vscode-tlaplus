import * as fs from 'fs/promises';
import { readFileSync } from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { LANG_TLAPLUS } from '../common';
import { SpecFiles } from './check';
import { runSany, SanyRunOptions } from '../tla2tools';
import { SanyData, SanyStdoutParser } from '../parsers/sany';

export interface SpecValidationOptions {
    documentOverrides?: Map<string, string>;
    dependencyRunner?: SanyRunner;
    validationRunner?: SanyRunner;
}

export interface SpecValidationResult {
    success: boolean;
    message?: string;
}

export interface SanyRunnerParams {
    readonly mode: 'dependency' | 'validation';
    readonly snapshotModulePath: string;
    readonly libraryPaths: string[];
    readonly snapshot: SnapshotState;
}

type SanyRunner = (params: SanyRunnerParams) => Promise<SanyData>;

interface SnapshotState {
    readonly rootDir: string;
    resolveOriginalToSnapshot(originalPath: string): string | undefined;
    resolveSnapshotToOriginal(snapshotPath: string): string | undefined;
    listSnapshotPaths(): string[];
}

const TEMP_DIR_PREFIX = 'tlaplus-model-snapshot-';

/**
 * Validates that the model `.tla` extends/instances the active spec using SANY as the single source of truth.
 */
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

    const overrides = options.documentOverrides ?? await collectOpenDocumentOverrides();
    const snapshot = await ModelSnapshot.create();
    try {
        await snapshot.addModule(specFiles.tlaFilePath, overrides);
        await snapshot.addModule(activeSpecPath, overrides);

        const modelSnapshotPath = snapshot.getSnapshotPath(specFiles.tlaFilePath);
        if (!modelSnapshotPath) {
            throw new Error(`Snapshot is missing model module ${specFiles.tlaFilePath}.`);
        }

        const dependencyRunner = options.dependencyRunner ?? defaultSanyRunner;
        const dependencyData = await dependencyRunner({
            mode: 'dependency',
            snapshotModulePath: modelSnapshotPath,
            libraryPaths: snapshot.getLibraryPaths(),
            snapshot: snapshot.getState()
        });

        await mirrorDependenciesIntoSnapshot(snapshot, dependencyData, overrides);

        const validationRunner = options.validationRunner ?? defaultSanyRunner;
        const validationData = await validationRunner({
            mode: 'validation',
            snapshotModulePath: modelSnapshotPath,
            libraryPaths: snapshot.getLibraryPaths(),
            snapshot: snapshot.getState()
        });

        return evaluateValidationResult(
            validationData,
            snapshot,
            activeSpecPath,
            overrides
        );
    } catch (err) {
        const message = err instanceof Error ? err.message : String(err);
        return {
            success: false,
            message: `Unable to validate model against active specification: ${message}`
        };
    } finally {
        await snapshot.dispose();
    }
}

async function defaultSanyRunner(params: SanyRunnerParams): Promise<SanyData> {
    const options: SanyRunOptions = { extraLibraryPaths: params.libraryPaths };
    const procInfo = await runSany(params.snapshotModulePath, options);
    const parser = new SanyStdoutParser(procInfo.process.stdout);
    return parser.readAll();
}

async function mirrorDependenciesIntoSnapshot(
    snapshot: ModelSnapshot,
    sanyData: SanyData,
    overrides: Map<string, string>
): Promise<void> {
    for (const modulePath of sanyData.modulePaths.values()) {
        if (!modulePath) {
            continue;
        }
        if (snapshot.isSnapshotPath(modulePath)) {
            continue;
        }
        if (isArchiveModulePath(modulePath)) {
            continue;
        }
        await snapshot.addModule(modulePath, overrides);
    }
}

function evaluateValidationResult(
    sanyData: SanyData,
    snapshot: ModelSnapshot,
    activeSpecPath: string,
    overrides: Map<string, string>
): SpecValidationResult {
    const expectedSnapshotPath = snapshot.getSnapshotPath(activeSpecPath);
    if (!expectedSnapshotPath) {
        return {
            success: false,
            message: `Snapshot is missing the active specification ${activeSpecPath}.`
        };
    }

    const specReferenced = Array.from(sanyData.modulePaths.values())
        .some((resolvedPath) => resolvedPath !== undefined
            && snapshot.pathsEqual(resolvedPath, expectedSnapshotPath));

    if (specReferenced) {
        return { success: true };
    }

    const specModuleName = inferModuleName(activeSpecPath, overrides) ?? path.basename(activeSpecPath);
    return {
        success: false,
        message: `Model does not EXTEND or INSTANCE module ${specModuleName}.`
    };
}

async function collectOpenDocumentOverrides(): Promise<Map<string, string>> {
    const normalize = normalizeFsPath;
    const overrides = new Map<string, string>();
    vscode.workspace.textDocuments
        .filter(doc => doc.languageId === LANG_TLAPLUS)
        .forEach(doc => overrides.set(normalize(doc.uri.fsPath), doc.getText()));
    return overrides;
}

function inferModuleName(modulePath: string, overrides: Map<string, string>): string | undefined {
    const normalized = normalizeFsPath(modulePath);
    const content = overrides.get(normalized);
    if (content) {
        return extractModuleName(content);
    }
    try {
        return extractModuleName(readFileSync(modulePath, 'utf8'));
    } catch {
        return undefined;
    }
}

function extractModuleName(content: string): string | undefined {
    const match = content.match(/^\s*-{4,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{4,}/m);
    return match ? match[1] : undefined;
}

class ModelSnapshot {
    private constructor(
        readonly rootDir: string
    ) {}

    private readonly originalToSnapshot = new Map<string, string>();
    private readonly snapshotToOriginal = new Map<string, string>();
    private readonly fallbackDirs = new Set<string>();

    static async create(): Promise<ModelSnapshot> {
        const rootDir = await fs.mkdtemp(path.join(os.tmpdir(), TEMP_DIR_PREFIX));
        return new ModelSnapshot(rootDir);
    }

    getState(): SnapshotState {
        return {
            rootDir: this.rootDir,
            resolveOriginalToSnapshot: (originalPath: string) => this.getSnapshotPath(originalPath),
            resolveSnapshotToOriginal: (snapshotPath: string) => this.snapshotToOriginal.get(normalizeFsPath(snapshotPath)),
            listSnapshotPaths: () => Array.from(this.snapshotToOriginal.keys())
        };
    }

    getSnapshotPath(originalPath: string): string | undefined {
        return this.originalToSnapshot.get(normalizeFsPath(originalPath));
    }

    isSnapshotPath(candidate: string): boolean {
        const normalizedRoot = normalizeFsPath(this.rootDir);
        const normalizedCandidate = normalizeFsPath(candidate);
        return normalizedCandidate.startsWith(normalizedRoot);
    }

    pathsEqual(pathA: string, pathB: string): boolean {
        return normalizeFsPath(pathA) === normalizeFsPath(pathB);
    }

    getLibraryPaths(): string[] {
        return [this.rootDir, ...Array.from(this.fallbackDirs)];
    }

    async addModule(originalPath: string, overrides: Map<string, string>): Promise<void> {
        const normalizedOriginal = normalizeFsPath(originalPath);
        if (this.originalToSnapshot.has(normalizedOriginal)) {
            return;
        }

        const content = overrides.get(normalizedOriginal) ?? await fs.readFile(originalPath, 'utf8');
        const relative = deriveSnapshotRelativePath(originalPath);
        const targetPath = path.join(this.rootDir, relative);

        await fs.mkdir(path.dirname(targetPath), { recursive: true });
        await fs.writeFile(targetPath, content, 'utf8');

        this.originalToSnapshot.set(normalizedOriginal, targetPath);
        this.snapshotToOriginal.set(normalizeFsPath(targetPath), normalizedOriginal);
        this.fallbackDirs.add(path.dirname(originalPath));
    }

    async dispose(): Promise<void> {
        try {
            await fs.rm(this.rootDir, { recursive: true, force: true });
        } catch {
            // Best-effort cleanup
        }
    }
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
    return path.join(...parts);
}

function normalizeFsPath(fsPath: string): string {
    const resolved = path.resolve(fsPath);
    return process.platform === 'win32' ? resolved.toLowerCase() : resolved;
}

function isArchiveModulePath(modulePath: string): boolean {
    return modulePath.startsWith('jar:file:') || modulePath.startsWith('jarfile:');
}
