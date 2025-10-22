import * as fs from 'fs/promises';
import { readFileSync } from 'fs';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG } from '../common';
import { SpecFiles } from './check';
import { runSany, SanyRunOptions } from '../tla2tools';
import { SanyData, SanyStdoutParser } from '../parsers/sany';

export interface SpecValidationOptions {
    documentOverrides?: Map<string, string>;
    dependencyRunner?: SanyRunner;
    validationRunner?: SanyRunner;
    retainSnapshot?: boolean;
}

export interface SpecValidationResult {
    success: boolean;
    message?: string;
    snapshot?: ValidationSnapshot;
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

export interface ValidationSnapshot {
    readonly modelPath: string;
    readonly configPath?: string;
    readonly libraryPaths: string[];
    resolveSnapshotToOriginal(snapshotPath: string): string | undefined;
    dispose(): Promise<void>;
}

/**
 * Validates that the model `.tla` extends/instances the active spec using SANY as the single source of truth.
 */
export async function validateModelSpecPair(
    specFiles: SpecFiles,
    activeSpecPath?: string,
    options: SpecValidationOptions = {}
): Promise<SpecValidationResult> {
    const normalize = normalizeFsPath;
    const normalizedModelPath = normalize(specFiles.tlaFilePath);

    const expectedSpecPaths = new Map<string, string>();
    if (activeSpecPath) {
        const normalizedActiveSpec = normalize(activeSpecPath);
        if (normalizedActiveSpec !== normalizedModelPath) {
            expectedSpecPaths.set(normalizedActiveSpec, activeSpecPath);
        }
    }

    const overrides = options.documentOverrides ?? await collectOpenDocumentOverrides();
    const expectedSpecModuleNames = await extractExpectedSpecModuleNames(
        specFiles,
        activeSpecPath,
        overrides,
        normalizedModelPath
    );

    const snapshot = await ModelSnapshot.create();
    const retainSnapshot = options.retainSnapshot === true;
    let snapshotRetained = false;
    try {
        await snapshot.addModule(specFiles.tlaFilePath, overrides);
        if (activeSpecPath && normalize(activeSpecPath) !== normalizedModelPath) {
            await snapshot.addModule(activeSpecPath, overrides);
        }
        await addConfigToSnapshotIfAvailable(snapshot, specFiles.cfgFilePath, overrides);

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

        const dependencyError = findSanyError(dependencyData, snapshot);
        if (dependencyError) {
            return {
                success: false,
                message: dependencyError
            };
        }

        const dependencyModules = collectResolvedModules(dependencyData, snapshot);
        const dependencyByName = new Map<string, ResolvedModuleDescriptor>();
        for (const module of dependencyModules) {
            dependencyByName.set(module.moduleName, module);
            const normalizedCandidate = module.normalizedSnapshotPath ?? module.normalizedOriginalPath;
            if (!normalizedCandidate) {
                continue;
            }
            if (!expectedSpecModuleNames.has(module.moduleName)) {
                continue;
            }
            if (!expectedSpecPaths.has(normalizedCandidate)) {
                const labelPath = module.originalPath ?? module.snapshotPath ?? normalizedCandidate;
                expectedSpecPaths.set(normalizedCandidate, labelPath);
            }
        }

        pruneUnresolvedExpectedModuleNames(expectedSpecModuleNames, dependencyByName);

        if (activeSpecPath) {
            const normalizedActiveSpec = normalizeFsPath(activeSpecPath);
            expectedSpecPaths.delete(normalizedActiveSpec);
            const snapshotSpecPath = snapshot.getSnapshotPath(activeSpecPath);
            if (snapshotSpecPath) {
                expectedSpecPaths.set(normalizeFsPath(snapshotSpecPath), activeSpecPath);
            }
        }

        await mirrorDependenciesIntoSnapshot(snapshot, dependencyData, overrides);

        for (const moduleName of expectedSpecModuleNames) {
            const descriptor = dependencyByName.get(moduleName);
            const originalPath = descriptor?.originalPath;
            if (!originalPath) {
                continue;
            }
            const normalizedOriginal = normalizeFsPath(originalPath);
            const snapshotPath = snapshot.getSnapshotPath(originalPath);
            if (snapshotPath) {
                expectedSpecPaths.delete(normalizedOriginal);
                expectedSpecPaths.set(normalizeFsPath(snapshotPath), originalPath);
            }
        }

        const validationRunner = options.validationRunner ?? defaultSanyRunner;
        const validationData = await validationRunner({
            mode: 'validation',
            snapshotModulePath: modelSnapshotPath,
            libraryPaths: snapshot.getLibraryPaths(),
            snapshot: snapshot.getState()
        });

        const validationError = findSanyError(validationData, snapshot);
        if (validationError) {
            return {
                success: false,
                message: validationError
            };
        }

        const evaluation = evaluateValidationResult(
            validationData,
            snapshot,
            specFiles,
            overrides,
            expectedSpecPaths,
            expectedSpecModuleNames
        );

        if (!evaluation.success) {
            return evaluation;
        }

        if (!retainSnapshot) {
            return evaluation;
        }

        const retainedSnapshot = createValidationSnapshot(snapshot, specFiles, overrides);
        snapshotRetained = true;
        return {
            ...evaluation,
            snapshot: retainedSnapshot
        };
    } catch (err) {
        const message = err instanceof Error ? err.message : String(err);
        return {
            success: false,
            message: `Unable to validate model specification pairing: ${message}`
        };
    } finally {
        if (!snapshotRetained) {
            await snapshot.dispose();
        }
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
        if (!(await pathExists(modulePath))) {
            continue;
        }
        await snapshot.addModule(modulePath, overrides);
    }
}

interface ResolvedModuleDescriptor {
    readonly moduleName: string;
    readonly snapshotPath?: string;
    readonly originalPath?: string;
    readonly normalizedSnapshotPath?: string;
    readonly normalizedOriginalPath?: string;
    readonly isArchive: boolean;
}

function collectResolvedModules(sanyData: SanyData, snapshot: ModelSnapshot): ResolvedModuleDescriptor[] {
    const descriptors: ResolvedModuleDescriptor[] = [];
    const snapshotState = snapshot.getState();
    for (const [moduleName, modulePathRaw] of sanyData.modulePaths.entries()) {
        if (!modulePathRaw) {
            continue;
        }
        if (isArchiveModulePath(modulePathRaw)) {
            descriptors.push({ moduleName, isArchive: true });
            continue;
        }
        const normalizedSnapshotPath = normalizeFsPath(modulePathRaw);
        let originalPath: string | undefined;
        if (snapshot.isSnapshotPath(normalizedSnapshotPath)) {
            originalPath = snapshotState.resolveSnapshotToOriginal(normalizedSnapshotPath);
        } else {
            originalPath = modulePathRaw;
        }
        descriptors.push({
            moduleName,
            snapshotPath: modulePathRaw,
            originalPath,
            normalizedSnapshotPath,
            normalizedOriginalPath: originalPath ? normalizeFsPath(originalPath) : undefined,
            isArchive: false
        });
    }
    return descriptors;
}

function pruneUnresolvedExpectedModuleNames(
    expectedNames: Set<string>,
    resolvedByName: Map<string, ResolvedModuleDescriptor>
): void {
    for (const name of Array.from(expectedNames)) {
        if (!resolvedByName.has(name)) {
            expectedNames.delete(name);
        }
    }
}

function findSanyError(sanyData: SanyData, snapshot: ModelSnapshot): string | undefined {
    for (const message of sanyData.dCollection.getMessages()) {
        if (message.diagnostic.severity !== vscode.DiagnosticSeverity.Error) {
            continue;
        }
        const displayPath = resolveSnapshotDisplayPath(snapshot, message.filePath);
        const location = displayPath ? `${path.basename(displayPath)}: ` : '';
        return `${location}${message.diagnostic.message}`;
    }
    return undefined;
}

function resolveSnapshotDisplayPath(snapshot: ModelSnapshot, fsPath: string): string | undefined {
    if (!fsPath) {
        return undefined;
    }
    if (snapshot.isSnapshotPath(fsPath)) {
        const resolved = snapshot.getState().resolveSnapshotToOriginal(fsPath);
        return resolved ?? fsPath;
    }
    return fsPath;
}

function evaluateValidationResult(
    sanyData: SanyData,
    snapshot: ModelSnapshot,
    specFiles: SpecFiles,
    overrides: Map<string, string>,
    expectedSpecPaths: Map<string, string>,
    expectedSpecModuleNames: Set<string>
): SpecValidationResult {
    const normalizedModelPath = normalizeFsPath(specFiles.tlaFilePath);
    const resolvedModules = collectResolvedModules(sanyData, snapshot);

    const matchedByPath = resolvedModules.some((module) => {
        const normalizedCandidate = module.normalizedSnapshotPath ?? module.normalizedOriginalPath;
        return normalizedCandidate !== undefined && expectedSpecPaths.has(normalizedCandidate);
    });
    const matchedByName = expectedSpecPaths.size === 0 && resolvedModules.some((module) =>
        expectedSpecModuleNames.has(module.moduleName));

    if (expectedSpecPaths.size > 0 || expectedSpecModuleNames.size > 0) {
        if (matchedByPath || matchedByName) {
            return { success: true };
        }

        const messageTarget = determineMissingSpecLabel(expectedSpecModuleNames, expectedSpecPaths, overrides);
        return {
            success: false,
            message: `Model does not EXTEND or INSTANCE module ${messageTarget}.`
        };
    }

    const referencesWorkspaceModule = resolvedModules.some((module) => {
        if (module.isArchive) {
            return false;
        }
        const candidate = module.normalizedOriginalPath ?? module.normalizedSnapshotPath;
        if (!candidate) {
            return false;
        }
        return candidate !== normalizedModelPath;
    });

    if (referencesWorkspaceModule) {
        return { success: true };
    }

    return {
        success: false,
        message: 'Model does not EXTEND or INSTANCE any specification module.'
    };
}

function determineMissingSpecLabel(
    expectedSpecModuleNames: Set<string>,
    expectedSpecPaths: Map<string, string>,
    overrides: Map<string, string>
): string {
    const firstName = expectedSpecModuleNames.values().next();
    if (!firstName.done) {
        return firstName.value;
    }
    const firstPathEntry = expectedSpecPaths.values().next();
    if (!firstPathEntry.done) {
        const candidatePath = firstPathEntry.value;
        return inferModuleName(candidatePath, overrides) ?? path.basename(candidatePath);
    }
    return 'the referenced specification';
}

async function pathExists(candidate: string): Promise<boolean> {
    try {
        await fs.access(candidate);
        return true;
    } catch {
        return false;
    }
}

async function collectOpenDocumentOverrides(): Promise<Map<string, string>> {
    const normalize = normalizeFsPath;
    const overrides = new Map<string, string>();
    vscode.workspace.textDocuments
        .filter(doc => doc.languageId === LANG_TLAPLUS || doc.languageId === LANG_TLAPLUS_CFG)
        .forEach(doc => overrides.set(normalize(doc.uri.fsPath), doc.getText()));
    return overrides;
}

async function extractExpectedSpecModuleNames(
    specFiles: SpecFiles,
    activeSpecPath: string | undefined,
    overrides: Map<string, string>,
    normalizedModelPath: string
): Promise<Set<string>> {
    const expectedNames = new Set<string>();

    if (activeSpecPath) {
        const normalizedActiveSpec = normalizeFsPath(activeSpecPath);
        if (normalizedActiveSpec !== normalizedModelPath) {
            const moduleName = inferModuleName(activeSpecPath, overrides);
            if (moduleName) {
                expectedNames.add(moduleName);
            }
        }
    }

    const configNames = await extractSpecModuleNamesFromConfig(specFiles.cfgFilePath, overrides);
    for (const name of configNames) {
        expectedNames.add(name);
    }

    return expectedNames;
}

async function extractSpecModuleNamesFromConfig(
    cfgPath: string,
    overrides: Map<string, string>
): Promise<Set<string>> {
    const names = new Set<string>();
    const normalizedCfgPath = normalizeFsPath(cfgPath);
    let content = overrides.get(normalizedCfgPath);
    if (!content) {
        try {
            content = await fs.readFile(cfgPath, 'utf8');
        } catch {
            return names;
        }
    }

    const lines = content.split(/\r?\n/);
    for (const line of lines) {
        const trimmed = line.trim();
        if (trimmed.length === 0 || trimmed.startsWith('\\*')) {
            continue;
        }
        const match = /^SPECIFICATION\s+([A-Za-z0-9_]+)/i.exec(trimmed);
        if (match) {
            names.add(match[1]);
        }
    }
    return names;
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
    const match = RegExp(/^\s*-{4,}\s*MODULE\s+([A-Za-z0-9_]+)\s*-{4,}/m).exec(content);
    return match ? match[1] : undefined;
}

function createValidationSnapshot(
    snapshot: ModelSnapshot,
    specFiles: SpecFiles,
    overrides: Map<string, string>
): ValidationSnapshot {
    const modelSnapshotPath = snapshot.getSnapshotPath(specFiles.tlaFilePath);
    if (!modelSnapshotPath) {
        throw new Error(`Snapshot is missing model module ${specFiles.tlaFilePath}.`);
    }
    const configSnapshotPath = snapshot.getSnapshotPath(specFiles.cfgFilePath);
    if (!configSnapshotPath) {
        const normalizedCfg = normalizeFsPath(specFiles.cfgFilePath);
        if (overrides.has(normalizedCfg)) {
            throw new Error(`Snapshot is missing overridden config ${specFiles.cfgFilePath}.`);
        }
    }
    return new RetainedSnapshot(snapshot, modelSnapshotPath, configSnapshotPath);
}

class ModelSnapshot {
    private constructor(
        readonly rootDir: string
    ) { }

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

async function addConfigToSnapshotIfAvailable(
    snapshot: ModelSnapshot,
    cfgPath: string,
    overrides: Map<string, string>
): Promise<void> {
    const normalizedCfg = normalizeFsPath(cfgPath);
    if (!overrides.has(normalizedCfg) && !(await pathExists(cfgPath))) {
        return;
    }
    await snapshot.addModule(cfgPath, overrides);
}

class RetainedSnapshot implements ValidationSnapshot {
    private disposed = false;

    constructor(
        private readonly snapshot: ModelSnapshot,
        readonly modelPath: string,
        readonly configPath: string | undefined
    ) {}

    get libraryPaths(): string[] {
        return this.snapshot.getLibraryPaths();
    }

    resolveSnapshotToOriginal(snapshotPath: string): string | undefined {
        return this.snapshot.getState().resolveSnapshotToOriginal(snapshotPath);
    }

    async dispose(): Promise<void> {
        if (this.disposed) {
            return;
        }
        this.disposed = true;
        await this.snapshot.dispose();
    }
}
