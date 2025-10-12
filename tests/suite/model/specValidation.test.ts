import * as assert from 'assert';
import * as fs from 'fs/promises';
import * as os from 'os';
import * as path from 'path';
import { afterEach } from 'mocha';
import { SpecFiles } from '../../../src/model/check';
import { validateModelSpecPair, SpecValidationOptions } from '../../../src/model/specValidation';
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

        const result = await validateModelSpecPair(specFiles, path.join(workDir, 'Spec.tla'), {
            sanyRunner: createSnapshotAwareSanyRunner()
        });

        assert.strictEqual(result.success, true);
    });

    test('fails when spec module not referenced', async () => {
        await createWorkspace();
        await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Other');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await fs.writeFile(specFiles.cfgFilePath, '');

        const result = await validateModelSpecPair(specFiles, path.join(workDir, 'Spec.tla'), {
            sanyRunner: async (modelSnapshotPath) => {
                const data = new SanyData();
                const modelName = await readModuleName(modelSnapshotPath);
                data.modulePaths.set(modelName ?? 'MCSpec', modelSnapshotPath);
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
            sanyRunner: async (modelSnapshotPath, _libraryDirs) => {
                const data = new SanyData();
                const modelName = await readModuleName(modelSnapshotPath);
                const specName = await readModuleName(specPath);
                if (modelName) {
                    data.modulePaths.set(modelName, modelSnapshotPath);
                }
                if (specName) {
                    data.modulePaths.set(specName, specPath);
                }
                return data;
            }
        });

        assert.strictEqual(result.success, false);
        assert.ok(result.message && result.message.includes('not the active module'));
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

        const result = await validateModelSpecPair(specFiles, specPath, {
            sanyRunner: createSnapshotAwareSanyRunner(),
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

    function createSnapshotAwareSanyRunner(): SpecValidationOptions['sanyRunner'] {
        return async (modelSnapshotPath, libraryDirs) => {
            const data = new SanyData();
            const modelName = await readModuleName(modelSnapshotPath);
            if (modelName) {
                data.modulePaths.set(modelName, modelSnapshotPath);
            }
            const specSnapshotPath = await findFileInDirs(libraryDirs, 'Spec.tla');
            if (specSnapshotPath) {
                const specName = await readModuleName(specSnapshotPath);
                if (specName) {
                    data.modulePaths.set(specName, specSnapshotPath);
                }
            }
            return data;
        };
    }

    async function findFileInDirs(dirs: string[], fileName: string): Promise<string | undefined> {
        for (const dir of dirs) {
            const candidate = path.join(dir, fileName);
            try {
                await fs.stat(candidate);
                return candidate;
            } catch {
                continue;
            }
        }
        return undefined;
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
