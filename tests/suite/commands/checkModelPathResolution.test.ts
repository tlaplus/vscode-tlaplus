import * as assert from 'assert';
import * as fs from 'fs/promises';
import * as os from 'os';
import * as path from 'path';
import * as vscode from 'vscode';
import fc from 'fast-check';
import { getValidationSpecPath } from '../../../src/commands/checkModel';

suite('checkModel spec path resolution', () => {
    const originalDescriptor = Object.getOwnPropertyDescriptor(vscode.window, 'activeTextEditor');

    teardown(() => {
        if (originalDescriptor) {
            Object.defineProperty(vscode.window, 'activeTextEditor', originalDescriptor);
        }
    });

    test('returns the same path when launched from a .tla editor', () => {
        const tlaPath = path.join('/workspace', 'Spec.tla');
        const specUri = vscode.Uri.file(tlaPath);
        setActiveEditor(fakeEditor(specUri, 'tlaplus'));

        const resolved = getValidationSpecPath(specUri);
        assert.strictEqual(resolved, tlaPath);
    });

    test('falls back to active .tla editor when launching from .cfg', () => {
        const specPath = path.join('/workspace', 'Spec.tla');
        const cfgPath = path.join('/workspace', 'MCSpec.cfg');
        const cfgUri = vscode.Uri.file(cfgPath);
        setActiveEditor(fakeEditor(vscode.Uri.file(specPath), 'tlaplus'));

        const resolved = getValidationSpecPath(cfgUri);
        assert.strictEqual(resolved, specPath);
    });

    test('falls back to companion .tla when no spec editor is active', () => {
        const cfgPath = path.join('/workspace', 'MCSpec.cfg');
        const cfgUri = vscode.Uri.file(cfgPath);
        setActiveEditor(fakeEditor(vscode.Uri.file('/workspace/Readme.md'), 'markdown'));

        const resolved = getValidationSpecPath(cfgUri);
        assert.strictEqual(resolved, path.join('/workspace', 'MCSpec.tla'));
    });

    test('resolves SPEC directive from config when no spec editor is active', async () => {
        const workDir = await fs.mkdtemp(path.join(os.tmpdir(), 'tlaplus-spec-path-'));
        const specPath = path.join(workDir, 'Spec.tla');
        const cfgPath = path.join(workDir, 'MCSpec.cfg');
        await fs.writeFile(cfgPath, 'SPECIFICATION Spec\n');
        setActiveEditor(undefined);

        const resolved = getValidationSpecPath(vscode.Uri.file(cfgPath));
        assert.strictEqual(resolved, specPath);
    });

    test('property: launching from cfg uses SPEC directive regardless of active tab', async () => {
        const workDir = await fs.mkdtemp(path.join(os.tmpdir(), 'tlaplus-spec-path-prop-'));
        const specPath = path.join(workDir, 'Spec.tla');
        const cfgPath = path.join(workDir, 'MCSpec.cfg');
        await fs.writeFile(cfgPath, 'SPECIFICATION Spec\n');
        const cfgUri = vscode.Uri.file(cfgPath);

        const activeKinds = fc.constantFrom<'tlaplus' | 'tlaplus_cfg' | 'markdown' | 'undefined'> (
            'tlaplus', 'tlaplus_cfg', 'markdown', 'undefined'
        );

        await fc.assert(fc.asyncProperty(activeKinds, async (activeKind) => {
            const activeEditor = (() => {
                if (activeKind === 'undefined') {
                    return undefined;
                }
                const languageId = activeKind === 'tlaplus_cfg' ? 'tlaplus_cfg' : activeKind;
                const suffix = activeKind === 'tlaplus' ? 'OtherSpec.tla'
                    : activeKind === 'tlaplus_cfg' ? 'Other.cfg' : 'notes.md';
                return fakeEditor(vscode.Uri.file(path.join(workDir, suffix)), languageId);
            })();

            setActiveEditor(activeEditor);
            const resolved = getValidationSpecPath(cfgUri);
            assert.strictEqual(resolved, specPath);
        }), { numRuns: 20 });
    });

    test('property: random editor focus sequences still resolve config SPEC', async () => {
        const workDir = await fs.mkdtemp(path.join(os.tmpdir(), 'tlaplus-spec-path-seq-'));
        const specPath = path.join(workDir, 'Spec.tla');
        const cfgPath = path.join(workDir, 'MCSpec.cfg');
        await fs.writeFile(cfgPath, 'SPECIFICATION Spec\n');
        const cfgUri = vscode.Uri.file(cfgPath);

        const actions = fc.array(fc.constantFrom('focusSpec', 'focusModel', 'focusOther', 'close'), { minLength: 1, maxLength: 10 });

        await fc.assert(fc.asyncProperty(actions, async (sequence) => {
            let currentEditor: vscode.TextEditor | undefined = undefined;

            const apply = (action: string) => {
                switch (action) {
                    case 'focusSpec':
                        currentEditor = fakeEditor(vscode.Uri.file(path.join(workDir, 'Spec.tla')), 'tlaplus');
                        break;
                    case 'focusModel':
                        currentEditor = fakeEditor(vscode.Uri.file(path.join(workDir, 'MCSpec.tla')), 'tlaplus');
                        break;
                    case 'focusOther':
                        currentEditor = fakeEditor(vscode.Uri.file(path.join(workDir, 'notes.md')), 'markdown');
                        break;
                    case 'close':
                        currentEditor = undefined;
                        break;
                    default:
                        break;
                }
                setActiveEditor(currentEditor);
            };

            sequence.forEach(apply);
            const resolved = getValidationSpecPath(cfgUri);
            assert.strictEqual(resolved, specPath);
        }), { numRuns: 20 });
    });

    test('property: config variants (SPEC, INIT, none) resolve or return undefined appropriately', async () => {
        const workDir = await fs.mkdtemp(path.join(os.tmpdir(), 'tlaplus-spec-path-cfg-variants-'));
        const cfgBase = path.join(workDir, 'Model');

        const cfgContentArb = fc.oneof(
            fc.constant('SPECIFICATION Spec\n'),
            fc.constant('INIT InitSpec\n'),
            fc.constant('')
        );

        await fc.assert(fc.asyncProperty(cfgContentArb, async (cfgContent) => {
            const cfgPath = `${cfgBase}.cfg`;
            await fs.writeFile(cfgPath, cfgContent);
            setActiveEditor(undefined);

            const resolved = getValidationSpecPath(vscode.Uri.file(cfgPath));
            if (cfgContent.startsWith('SPECIFICATION')) {
                assert.strictEqual(resolved, path.join(workDir, 'Spec.tla'));
            } else if (cfgContent.startsWith('INIT')) {
                assert.strictEqual(resolved, path.join(workDir, 'Model.tla'));
            } else {
                assert.strictEqual(resolved, `${cfgBase}.tla`);
            }
        }), { numRuns: 10 });
    });


    function setActiveEditor(editor: vscode.TextEditor | undefined): void {
        Object.defineProperty(vscode.window, 'activeTextEditor', {
            configurable: true,
            get: () => editor
        });
    }

    function fakeEditor(uri: vscode.Uri, languageId: string): vscode.TextEditor {
        return {
            document: {
                languageId,
                uri
            }
        } as unknown as vscode.TextEditor;
    }
});
