import * as assert from 'assert';
import * as fs from 'fs/promises';
import * as os from 'os';
import * as path from 'path';
import { afterEach } from 'mocha';
import fc from 'fast-check';
import { SpecFiles } from '../../../src/model/check';
import { validateModelSpecPair, SanyRunnerParams } from '../../../src/model/specValidation';
import { SanyData } from '../../../src/parsers/sany';
import * as vscode from 'vscode';

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
        await writeConfig(specFiles.cfgFilePath, 'Spec');

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
        await writeConfig(specFiles.cfgFilePath, 'Spec');

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
        assert.ok(result?.message?.includes('does not EXTEND'));
    });

    test('passes when active spec is the model module itself', async () => {
        await createWorkspace();
        const modelPath = path.join(workDir, 'MCSpec.tla');
        await fs.writeFile(modelPath, [
            '---- MODULE MCSpec ----',
            'ASSUME TRUE',
            '===='
        ].join('\n'));
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await fs.writeFile(specFiles.cfgFilePath, '');

        const runner = async (params: SanyRunnerParams) => {
            const data = new SanyData();
            const modelName = await readModuleName(params.snapshotModulePath);
            if (modelName) {
                data.modulePaths.set(modelName, params.snapshotModulePath);
            }
            return data;
        };

        const result = await validateModelSpecPair(specFiles, modelPath, {
            dependencyRunner: runner,
            validationRunner: runner
        });

        assert.strictEqual(result.success, true);
    });

    test('fails when model resolves different spec path', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

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

        const overrides = new Map<string, string>();
        const newSpecName = 'SpecUnsaved';
        const newModelName = 'MCSpecUnsaved';
        await writeConfig(specFiles.cfgFilePath, newSpecName);
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

    test('accepts SPECIFICATION formula names that differ from module name', async () => {
        await createWorkspace();
        const specPath = path.join(workDir, 'MRE.tla');
        await fs.writeFile(specPath, [
            '---- MODULE MRE ----',
            'EXTENDS Naturals',
            'VARIABLE x',
            'Init == x = 0',
            'Next == x\' = x + 1',
            'Spec == Init /\\ [][Next]_x',
            '===='
        ].join('\n'));
        const modelPath = await writeModel('MCSpec', 'MRE');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const runners = createSanyRunners(specPath, modelPath);
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: runners.dependency,
            validationRunner: runners.validation
        });

        assert.strictEqual(result.success, true);
    });

    test('fails for unsaved model override when active spec provided', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const overrides = new Map<string, string>();
        overrides.set(normalizeForOverride(modelPath), tlaModelModule('MCSpec', 'Blablabla'));

        const sanyWithoutSpec = createRunnerWithError(modelPath, 'Blablabla');
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: sanyWithoutSpec,
            validationRunner: sanyWithoutSpec,
            documentOverrides: overrides
        });

        assert.strictEqual(result.success, false);
        assert.ok(result.message && result.message.includes('Blablabla'));
    });

    test('fails for unsaved model override without explicit spec path', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const overrides = new Map<string, string>();
        overrides.set(normalizeForOverride(modelPath), tlaModelModule('MCSpec', 'Blablabla'));

        const sanyWithoutSpec = createRunnerWithError(modelPath, 'Blablabla');
        const result = await validateModelSpecPair(specFiles, undefined, {
            dependencyRunner: sanyWithoutSpec,
            validationRunner: sanyWithoutSpec,
            documentOverrides: overrides
        });

        assert.strictEqual(result.success, false);
        assert.ok(result.message && result.message.includes('Blablabla'));
    });

    test('fails without explicit spec path when config expects module', async () => {
        await createWorkspace();
        await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Other');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const result = await validateModelSpecPair(specFiles, undefined, {
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
        assert.ok(result.message && result.message.includes('any specification module'));
    });

    test('passes without explicit spec path when config module resolved', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const runners = createSanyRunners(specPath, modelPath);
        const result = await validateModelSpecPair(specFiles, undefined, {
            dependencyRunner: runners.dependency,
            validationRunner: runners.validation
        });

        assert.strictEqual(result.success, true);
    });

    test('skips missing dependency modules gracefully', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const runners = createSanyRunners(specPath, modelPath);
        const missingDependencyPath = path.join(os.tmpdir(), 'tlaplus-non-existent', 'Integers.tla');

        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: async (params) => {
                const data = await runners.dependency(params);
                data.modulePaths.set('Integers', missingDependencyPath);
                return data;
            },
            validationRunner: runners.validation
        });

        assert.strictEqual(result.success, true);
    });

    test('fails fast on SANY diagnostic errors', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const errorRunner = createRunnerWithError(modelPath, 'Blablabla');
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: errorRunner,
            validationRunner: errorRunner
        });

        assert.strictEqual(result.success, false);
        assert.ok(result.message && result.message.includes('Blablabla'));
    });

    test('regression: cfg launch with missing module and dirty spec blocks TLC', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const overrides = new Map<string, string>();
        overrides.set(normalizeForOverride(specPath), tlaModule('SpecDirty'));
        overrides.set(normalizeForOverride(modelPath), [
            '---- MODULE MCSpec ----',
            'EXTENDS Blablabla',
            '===='
        ].join('\n'));

        const errorRunner = createRunnerWithError(modelPath, 'Blablabla');
        const result = await validateModelSpecPair(specFiles, undefined, {
            dependencyRunner: errorRunner,
            validationRunner: errorRunner,
            documentOverrides: overrides
        });

        assert.strictEqual(result.success, false);
        assert.ok(result.message && result.message.includes('Blablabla'));
    });

    test('retains snapshot when requested', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const runners = createSanyRunners(specPath, modelPath);
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: runners.dependency,
            validationRunner: runners.validation,
            retainSnapshot: true
        });

        assert.strictEqual(result.success, true);
        assert.ok(result.snapshot, 'Snapshot should be returned on success');
        const snapshot = result.snapshot!;
        const modelSnapshotPath = snapshot.modelPath;
        const configSnapshotPath = snapshot.configPath;
        try {
            assert.ok(path.isAbsolute(modelSnapshotPath), 'Model snapshot path should be absolute');
            assert.ok(configSnapshotPath, 'Config snapshot path should be defined');
            assert.ok(snapshot.libraryPaths.some((p) => {
                const relative = path.relative(p, modelSnapshotPath);
                return relative === '' || !relative.startsWith('..');
            }), 'Snapshot library paths should include the model path');
            assertPathEquals(
                snapshot.resolveSnapshotToOriginal(modelSnapshotPath),
                specFiles.tlaFilePath
            );
            const configContent = await fs.readFile(configSnapshotPath!, 'utf8');
            const originalConfig = await fs.readFile(specFiles.cfgFilePath, 'utf8');
            assert.strictEqual(configContent, originalConfig);
        } finally {
            await snapshot.dispose();
        }
        await assert.rejects(fs.access(modelSnapshotPath));
    });

    test('retained snapshot prefers unsaved config overrides', async () => {
        await createWorkspace();
        const specPath = await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Spec');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const overrides = new Map<string, string>();
        const overrideContent = 'SPECIFICATION SpecUnsaved';
        overrides.set(normalizeForOverride(specFiles.cfgFilePath), overrideContent);

        const runners = createSanyRunners(specPath, modelPath);
        const result = await validateModelSpecPair(specFiles, specPath, {
            dependencyRunner: runners.dependency,
            validationRunner: runners.validation,
            documentOverrides: overrides,
            retainSnapshot: true
        });

        assert.strictEqual(result.success, true);
        assert.ok(result.snapshot);
        const snapshot = result.snapshot!;
        try {
            assert.ok(snapshot.configPath, 'Config snapshot path should be defined');
            const configContent = await fs.readFile(snapshot.configPath!, 'utf8');
            assert.strictEqual(configContent.trim(), overrideContent);
        } finally {
            await snapshot.dispose();
        }
    });

    test('does not retain snapshot when validation fails', async () => {
        await createWorkspace();
        await writeSpec('Spec');
        const modelPath = await writeModel('MCSpec', 'Other');
        const specFiles = new SpecFiles(modelPath, path.join(workDir, 'MCSpec.cfg'));
        await writeConfig(specFiles.cfgFilePath, 'Spec');

        const result = await validateModelSpecPair(specFiles, undefined, {
            dependencyRunner: async (params) => {
                const data = new SanyData();
                const modelName = await readModuleName(params.snapshotModulePath);
                if (modelName) {
                    data.modulePaths.set(modelName, params.snapshotModulePath);
                }
                return data;
            },
            validationRunner: async (params) => {
                const data = new SanyData();
                const modelName = await readModuleName(params.snapshotModulePath);
                if (modelName) {
                    data.modulePaths.set(modelName, params.snapshotModulePath);
                }
                data.dCollection.addMessage(
                    params.snapshotModulePath,
                    new vscode.Range(0, 0, 0, 0),
                    'Model does not EXTEND or INSTANCE module Spec',
                    vscode.DiagnosticSeverity.Error
                );
                return data;
            },
            retainSnapshot: true
        });

        assert.strictEqual(result.success, false);
        assert.strictEqual(result.snapshot, undefined);
    });

    test('property: spec/model saved and dirty permutations behave as expected', async () => {
        await createWorkspace();
        await fs.writeFile(path.join(workDir, 'Placeholder'), '');

        const arb = fc.record({
            specSaved: fc.boolean(),
            modelSaved: fc.boolean(),
            specMissingModule: fc.boolean(),
            modelMissingModule: fc.boolean(),
            configTargetsSpec: fc.boolean(),
            configTargetsOther: fc.boolean(),
            modelInstancesOnly: fc.boolean(),
            cfgHasSpecBlock: fc.boolean()
        });

        await fc.assert(fc.asyncProperty(arb, async (params) => {
            await fs.rm(workDir, { recursive: true, force: true });
            await createWorkspace();

            const specModule = params.specMissingModule ? 'SpecMissing' : 'Spec';
            const specPath = await writeSpec(specModule);
            const modelPath = await writeModel('MCSpec', params.modelMissingModule ? 'Blablabla' : specModule, params.modelInstancesOnly);
            const cfgPath = path.join(workDir, 'MCSpec.cfg');
            const specFiles = new SpecFiles(modelPath, cfgPath);

            if (params.cfgHasSpecBlock) {
                const target = params.configTargetsOther ? 'OtherSpec' : specModule;
                await writeConfig(cfgPath, target);
            } else {
                await fs.writeFile(cfgPath, '');
            }

            const overrides = new Map<string, string>();
            if (!params.specSaved) {
                overrides.set(normalizeForOverride(specPath), tlaModule(`${specModule}Dirty`));
            }
            if (!params.modelSaved) {
                const extendsTarget = params.modelMissingModule ? 'Blablabla' : specModule;
                overrides.set(normalizeForOverride(modelPath),
                    params.modelInstancesOnly
                        ? tlaModelInstanceOnly('MCSpecDirty', extendsTarget)
                        : tlaModelModule('MCSpecDirty', extendsTarget));
            }

            const dependencyRunner = params.modelMissingModule || params.specMissingModule
                ? createRunnerWithError(modelPath, params.modelMissingModule ? 'Blablabla' : specModule)
                : createSanyRunners(specPath, modelPath).dependency;

            const validationRunner = params.modelMissingModule || params.specMissingModule
                ? createRunnerWithError(modelPath, params.modelMissingModule ? 'Blablabla' : specModule)
                : createSanyRunners(specPath, modelPath).validation;

            const result = await validateModelSpecPair(
                specFiles,
                params.configTargetsOther ? undefined : specPath,
                {
                    dependencyRunner,
                    validationRunner,
                    documentOverrides: overrides
                }
            );

            if (params.modelMissingModule) {
                assert.strictEqual(result.success, false);
            }
        }), { numRuns: 50 });
    });

    async function createWorkspace(): Promise<void> {
        workDir = await fs.mkdtemp(path.join(os.tmpdir(), 'tlaplus-spec-validation-'));
    }

    async function writeSpec(moduleName: string): Promise<string> {
        const specPath = path.join(workDir, 'Spec.tla');
        await fs.writeFile(specPath, tlaModule(moduleName));
        return specPath;
    }

    async function writeModel(moduleName: string, targetSpec: string, instanceOnly = false): Promise<string> {
        const modelPath = path.join(workDir, `${moduleName}.tla`);
        const content = instanceOnly
            ? tlaModelInstanceOnly(moduleName, targetSpec)
            : tlaModelModule(moduleName, targetSpec);
        await fs.writeFile(modelPath, content);
        return modelPath;
    }

    async function writeConfig(cfgPath: string, specModuleName?: string): Promise<void> {
        const lines: string[] = [];
        if (specModuleName) {
            lines.push(`SPECIFICATION ${specModuleName}`);
        }
        await fs.writeFile(cfgPath, lines.join('\n'));
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

    function tlaModelInstanceOnly(moduleName: string, targetSpec: string): string {
        return [
            `---- MODULE ${moduleName} ----`,
            `INSTANCE ${targetSpec}`,
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
            const specCandidatePath = params.snapshot.resolveOriginalToSnapshot(specPath) ?? specPath;
            const specName = await readModuleName(specCandidatePath);
            if (specName) {
                data.modulePaths.set(specName, specCandidatePath);
            }
            return data;
        };

        const validation = async (params: SanyRunnerParams) => {
            const data = new SanyData();
            const modelName = await readModuleName(params.snapshotModulePath);
            if (modelName) {
                data.modulePaths.set(modelName, params.snapshotModulePath);
            }
            const specCandidatePath = params.snapshot.resolveOriginalToSnapshot(specPath) ?? specPath;
            const specName = await readModuleName(specCandidatePath);
            if (specName) {
                data.modulePaths.set(specName, specCandidatePath);
            }
            return data;
        };

        return { dependency, validation };
    }

    function createRunnerWithError(modelPath: string, missingModuleName: string) {
        return async (params: SanyRunnerParams) => {
            const data = new SanyData();
            const modelName = await readModuleName(params.snapshotModulePath);
            if (modelName) {
                data.modulePaths.set(modelName, params.snapshotModulePath);
            }
            const missingModulePath = path.join(path.dirname(modelPath), `${missingModuleName}.tla`);
            data.modulePaths.set(missingModuleName, missingModulePath);
            data.dCollection.addMessage(
                params.snapshotModulePath,
                new vscode.Range(0, 0, 0, 0),
                `Cannot find source file for module ${missingModuleName} imported in module ${modelName ?? 'model'}`,
                vscode.DiagnosticSeverity.Error
            );
            return data;
        };
    }

    async function readModuleName(fsPath: string): Promise<string | undefined> {
        try {
            const content = await fs.readFile(fsPath, 'utf8');
            const match = RegExp(/MODULE\s+([A-Za-z0-9_]+)/).exec(content);
            return match ? match[1] : undefined;
        } catch {
            return undefined;
        }
    }

});

function assertPathEquals(actual: string | undefined, expected: string | undefined): void {
    if (!actual || !expected) {
        assert.strictEqual(actual, expected);
        return;
    }
    assert.strictEqual(normalizeFsPath(actual), normalizeFsPath(expected));
}

function normalizeFsPath(fsPath: string): string {
    const resolved = path.resolve(fsPath);
    return process.platform === 'win32' ? resolved.toLowerCase() : resolved;
}
