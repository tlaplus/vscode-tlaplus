import * as assert from 'assert';
import * as fs from 'fs/promises';
import * as os from 'os';
import * as path from 'path';
import { afterEach } from 'mocha';
import { SpecFiles } from '../../../src/model/check';
import { validateModelSpecPair, SanyRunnerParams } from '../../../src/model/specValidation';
import { SanyData } from '../../../src/parsers/sany';

suite('Spec-Model Validation', () => {
    let workDir: string;

    afterEach(async () => {
        if (workDir) {
            await fs.rm(workDir, { recursive: true, force: true });
        }
    });

    test('passes when model references active spec', async () => {
        await createWorkspace();
        await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await fs.writeFile(specFiles.cfgFilePath, '');

        const specPath = path.join(workDir, 'Spec.tla');
        const runners = createSanyRunners(specPath, modelPath);
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: runners.dependency,
            validationRunner: runners.validation
        });

        assert.strictEqual(result.success, true);
    });

    test('fails when spec module not referenced', async () => {
        await createWorkspace();
        await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Other');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await fs.writeFile(specFiles.cfgFilePath, '');

        const specPath = path.join(workDir, 'Spec.tla');
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: async (params) => {
                const data = new SanyData();
                const modelName = await readModuleName(params.snapshotModulePath);
                data.modulePaths.set(modelName ?? 'MCSpec', params.snapshotModulePath);
                return data;
            },
            validationRunner: async (params) => {
                const data = new SanyData();
                const modelName = await readModuleName(params.snapshotModulePath);
                data.modulePaths.set(modelName ?? 'MCSpec', params.snapshotModulePath);
                return data;
            }
        });

        assert.strictEqual(result.success, false);
        assert.ok(result.message && result.message.includes('does not EXTEND'));
    });

    test('fails when model resolves different spec path', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await fs.writeFile(specFiles.cfgFilePath, '');

        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: async (params) => {
                const data = new SanyData();
                const modelName = await readModuleName(params.snapshotModulePath);
                if (modelName) {
                    data.modulePaths.set(modelName, params.snapshotModulePath);
                }
                const specSnapshot = params.snapshot.resolveOriginalToSnapshot(specPath);
                if (specSnapshot) {
                    const specName = await readModuleName(specSnapshot);
                    if (specName) {
                        data.modulePaths.set(specName, specSnapshot);
                    }
                }
                return data;
            },
            validationRunner: async (params) => {
                const data = new SanyData();
                const modelName = await readModuleName(params.snapshotModulePath);
                const specName = await readModuleName(specPath);
                if (modelName) {
                    data.modulePaths.set(modelName, params.snapshotModulePath);
                }
                if (specName) {
                    data.modulePaths.set(specName, specPath);
                }
                return data;
            }
        });

        assert.strictEqual(result.success, false);
        assert.ok(result.message && result.message.includes('does not EXTEND'));
    });

    test('uses overrides for unsaved buffers', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await fs.writeFile(specFiles.cfgFilePath, '');

        const overrides = new Map<string, string>();
        const newSpecName = 'SpecUnsaved';
        const newModelName = 'MCSpecUnsaved';
        overrides.set(normalizeForOverride(specPath), tlaModule(newSpecName));
        overrides.set(normalizeForOverride(modelPath), tlaModelModule(newModelName, newSpecName));

        const runners = createSanyRunners(specPath, modelPath);
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: runners.dependency,
            validationRunner: runners.validation,
            documentOverrides: overrides
        });

        assert.strictEqual(result.success, true);
    });

    async function createWorkspace(): Promise<void> {
        workDir = await fs.mkdtemp(path.join(os.tmpdir(), 'tlaplus-spec-validation-'));
    }

    async function writeSpec(moduleName: string): Promise<string> {
        const specPath = path.join(workDir, 'Spec.tla');
        await fs.writeFile(specPath, tlaModule(moduleName));
        return specPath;
    }

    async function writeModel(moduleName: string, targetSpec: string): Promise<string> {
        const modelPath = path.join(workDir, `${moduleName}.tla`);
        await fs.writeFile(modelPath, tlaModelModule(moduleName, targetSpec));
        return modelPath;
    }

    function tlaModule(moduleName: string): string {
        return [
            `---- MODULE ${moduleName} ----`,
            'EXTENDS Naturals',
            '===='
        ].join('\n');
    }

    function tlaModelModule(moduleName: string, targetSpec: string): string {
        return [
            `---- MODULE ${moduleName} ----`,
            `EXTENDS ${targetSpec}`,
            '===='
        ].join('\n');
    }

    function normalizeForOverride(fsPath: string): string {
        const resolved = path.resolve(fsPath);
        return process.platform === 'win32' ? resolved.toLowerCase() : resolved;
    }

    function createSanyRunners(specPath: string, modelPath: string) {
        const dependency = async (params: SanyRunnerParams) => {
            const data = new SanyData();
            const modelName = await readModuleName(params.snapshotModulePath);
            if (modelName) {
                data.modulePaths.set(modelName, params.snapshotModulePath);
            }
            const specSnapshotPath = params.snapshot.resolveOriginalToSnapshot(specPath);
            if (specSnapshotPath) {
                const specName = await readModuleName(specSnapshotPath);
                if (specName) {
                    data.modulePaths.set(specName, specSnapshotPath);
                }
            }
            return data;
        };

        const validation = async (params: SanyRunnerParams) => {
            const data = new SanyData();
            const modelName = await readModuleName(params.snapshotModulePath);
            if (modelName) {
                data.modulePaths.set(modelName, params.snapshotModulePath);
            }
            const specSnapshotPath = params.snapshot.resolveOriginalToSnapshot(specPath);
            if (specSnapshotPath) {
                const specName = await readModuleName(specSnapshotPath);
                if (specName) {
                    data.modulePaths.set(specName, specSnapshotPath);
                }
            }
            return data;
        };

        return { dependency, validation };
    }

    async function readModuleName(fsPath: string): Promise<string | undefined> {
        try {
            const content = await fs.readFile(fsPath, 'utf8');
            const match = content.match(/MODULE\s+([A-Za-z0-9_]+)/);
            return match ? match[1] : undefined;
        } catch {
            return undefined;
        }
    }
});
