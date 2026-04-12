import * as assert from 'assert';
import * as path from 'path';
import {
    buildModelEditorPaths,
    detectUnsupportedDirectives,
    discoverSpecInfo,
    parseModelEditorState,
    serializeModelEditorState,
    ModelEditorState
} from '../../../src/model/modelEditorFiles';

suite('Model editor files', () => {
    test('Builds MC-prefixed model file paths from a spec', () => {
        const paths = buildModelEditorPaths(path.join('/tmp', 'Spec.tla'));
        assert.strictEqual(paths.specName, 'Spec');
        assert.strictEqual(paths.modelName, 'MCSpec');
        assert.strictEqual(paths.tlaFilePath, path.join('/tmp', 'MCSpec.tla'));
        assert.strictEqual(paths.cfgFilePath, path.join('/tmp', 'MCSpec.cfg'));
    });

    test('Does not overwrite specs whose names already start with MC', () => {
        const paths = buildModelEditorPaths(path.join('/tmp', 'MCSpec.tla'));
        assert.strictEqual(paths.specName, 'MCSpec');
        assert.strictEqual(paths.modelName, 'MCMCSpec');
        assert.strictEqual(paths.tlaFilePath, path.join('/tmp', 'MCMCSpec.tla'));
        assert.strictEqual(paths.cfgFilePath, path.join('/tmp', 'MCMCSpec.cfg'));
    });

    test('Serializes editor state into TLC files', () => {
        const state: ModelEditorState = {
            specName: 'Spec',
            specPath: path.join('/tmp', 'Spec.tla'),
            modelName: 'MCSpec',
            behavior: {
                kind: 'initNext',
                init: 'Init',
                next: 'Next'
            },
            checkDeadlock: false,
            constants: [
                { name: 'N', kind: 'ordinary', value: '3' },
                { name: 'Nodes', kind: 'setModelValues', value: 'a, b' }
            ],
            invariants: ['TypeOK'],
            properties: ['Liveness'],
            stateConstraint: '',
            actionConstraint: '',
            definitionOverrides: [],
            additionalDefinitions: ''
        };

        const files = serializeModelEditorState(state);
        assert.match(files.tlaContent, /---- MODULE MCSpec ----/);
        assert.match(files.tlaContent, /EXTENDS Spec, TLC/);
        assert.match(files.cfgContent, /INIT Init/);
        assert.match(files.cfgContent, /NEXT Next/);
        assert.match(files.cfgContent, /CHECK_DEADLOCK FALSE/);
        assert.match(files.cfgContent, /CONSTANT N = 3/);
        assert.match(files.cfgContent, /CONSTANT Nodes = \{a, b\}/);
        assert.match(files.cfgContent, /INVARIANT TypeOK/);
        assert.match(files.cfgContent, /PROPERTY Liveness/);
    });

    test('Round-trips state from generated files', () => {
        const state: ModelEditorState = {
            specName: 'Spec',
            specPath: path.join('/tmp', 'Spec.tla'),
            modelName: 'MCSpec',
            behavior: {
                kind: 'temporal',
                temporal: 'Spec'
            },
            checkDeadlock: true,
            constants: [
                { name: 'Node', kind: 'modelValue', value: 'node_a' }
            ],
            invariants: ['TypeOK'],
            properties: [],
            stateConstraint: '',
            actionConstraint: '',
            definitionOverrides: [],
            additionalDefinitions: ''
        };

        const files = serializeModelEditorState(state);
        const parsed = parseModelEditorState(path.join('/tmp', 'Spec.tla'), files.tlaContent, files.cfgContent);
        assert.ok(parsed);
        assert.strictEqual(parsed?.behavior.kind, 'temporal');
        assert.strictEqual(parsed?.behavior.temporal, 'Spec');
        assert.deepStrictEqual(parsed?.constants, state.constants);
        assert.deepStrictEqual(parsed?.invariants, state.invariants);
    });

    test('Parses simple existing cfg content without editor metadata', () => {
        const parsed = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            [
                'CONSTANTS',
                '    greeting = "Hello"',
                '    Node <- node_a',
                'INIT Init',
                'NEXT Next',
                'INVARIANT TypeOK',
                'PROPERTY Liveness'
            ].join('\n')
        );

        assert.ok(parsed);
        assert.strictEqual(parsed?.behavior.kind, 'initNext');
        assert.strictEqual(parsed?.constants[0].name, 'greeting');
        assert.strictEqual(parsed?.constants[1].kind, 'modelValue');
        assert.deepStrictEqual(parsed?.invariants, ['TypeOK']);
        assert.deepStrictEqual(parsed?.properties, ['Liveness']);
    });

    test('Parses plural invariants/properties and constants across blank lines', () => {
        const parsed = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            [
                'CONSTANTS',
                '  a1 = a1  a2 = a2',
                '',
                '  a3 = a3',
                'INVARIANTS TypeOK Safety',
                'PROPERTIES Liveness Fairness'
            ].join('\n')
        );

        assert.ok(parsed);
        assert.deepStrictEqual(parsed?.constants.map((constant) => constant.name), ['a1', 'a2', 'a3']);
        assert.deepStrictEqual(parsed?.invariants, ['TypeOK', 'Safety']);
        assert.deepStrictEqual(parsed?.properties, ['Liveness', 'Fairness']);
    });

    test('Discovers parameterized constants without splitting on inner commas', () => {
        const discovered = discoverSpecInfo('CONSTANTS N(_, _), M, P(x)\nFoo == 1');
        assert.deepStrictEqual(discovered.constants, ['M', 'N(_, _)', 'P(x)']);
    });

    test('Detects unsupported directives in cfg content', () => {
        const cfg = [
            'INIT Init',
            'NEXT Next',
            'SYMMETRY Perms',
            'CONSTRAINT StateLimit',
            'ACTION_CONSTRAINT ActionLimit',
            'VIEW ViewExpr',
            'INVARIANT TypeOK'
        ].join('\n');
        const unsupported = detectUnsupportedDirectives(cfg);
        assert.deepStrictEqual(unsupported, ['SYMMETRY', 'VIEW']);
    });

    test('Returns empty list when cfg has only supported directives', () => {
        const cfg = [
            'INIT Init',
            'NEXT Next',
            'CHECK_DEADLOCK FALSE',
            'CONSTANT N = 3',
            'CONSTRAINT StateLimit',
            'ACTION_CONSTRAINT ActionLimit',
            'INVARIANT TypeOK',
            'PROPERTY Liveness'
        ].join('\n');
        assert.deepStrictEqual(detectUnsupportedDirectives(cfg), []);
    });

    test('Ignores comments when detecting unsupported directives', () => {
        const cfg = [
            '\\* SYMMETRY Perms',
            'INIT Init'
        ].join('\n');
        assert.deepStrictEqual(detectUnsupportedDirectives(cfg), []);
    });

    test('Serializes state constraint and action constraint', () => {
        const state: ModelEditorState = {
            specName: 'Spec',
            specPath: path.join('/tmp', 'Spec.tla'),
            modelName: 'MCSpec',
            behavior: { kind: 'initNext', init: 'Init', next: 'Next' },
            checkDeadlock: true,
            constants: [],
            invariants: [],
            properties: [],
            stateConstraint: 'StateLimit',
            actionConstraint: 'ActionLimit',
            definitionOverrides: [],
            additionalDefinitions: ''
        };

        const files = serializeModelEditorState(state);
        assert.match(files.cfgContent, /CONSTRAINT StateLimit/);
        assert.match(files.cfgContent, /ACTION_CONSTRAINT ActionLimit/);
    });

    test('Serializes definition overrides into cfg and tla', () => {
        const state: ModelEditorState = {
            specName: 'Spec',
            specPath: path.join('/tmp', 'Spec.tla'),
            modelName: 'MCSpec',
            behavior: { kind: 'initNext', init: 'Init', next: 'Next' },
            checkDeadlock: true,
            constants: [],
            invariants: [],
            properties: [],
            stateConstraint: '',
            actionConstraint: '',
            definitionOverrides: [
                { name: 'Nat', expression: '0..10' }
            ],
            additionalDefinitions: ''
        };

        const files = serializeModelEditorState(state);
        assert.match(files.cfgContent, /CONSTANT Nat <- MC_Nat/);
        assert.match(files.tlaContent, /MC_Nat == 0\.\.10/);
    });

    test('Serializes additional definitions into tla', () => {
        const state: ModelEditorState = {
            specName: 'Spec',
            specPath: path.join('/tmp', 'Spec.tla'),
            modelName: 'MCSpec',
            behavior: { kind: 'none' },
            checkDeadlock: true,
            constants: [],
            invariants: [],
            properties: [],
            stateConstraint: '',
            actionConstraint: '',
            definitionOverrides: [],
            additionalDefinitions: 'MaxVal == 10\nASSUME MaxVal > 0'
        };

        const files = serializeModelEditorState(state);
        assert.match(files.tlaContent, /MaxVal == 10/);
        assert.match(files.tlaContent, /ASSUME MaxVal > 0/);
        // Additional defs should appear before ====
        const eqIdx = files.tlaContent.indexOf('====');
        const defIdx = files.tlaContent.indexOf('MaxVal == 10');
        assert.ok(defIdx < eqIdx, 'Additional definitions must come before ====');
    });

    test('Parses constraint and action constraint from raw cfg', () => {
        const parsed = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            [
                'INIT Init',
                'NEXT Next',
                'CONSTRAINT StateLimit',
                'ACTION_CONSTRAINT ActionLimit'
            ].join('\n')
        );

        assert.ok(parsed);
        assert.strictEqual(parsed?.stateConstraint, 'StateLimit');
        assert.strictEqual(parsed?.actionConstraint, 'ActionLimit');
    });

    test('Parses definition overrides from raw cfg', () => {
        const parsed = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            [
                'INIT Init',
                'NEXT Next',
                'CONSTANT Nat <- MC_Nat'
            ].join('\n')
        );

        assert.ok(parsed);
        assert.strictEqual(parsed?.definitionOverrides.length, 1);
        assert.strictEqual(parsed?.definitionOverrides[0].name, 'Nat');
        assert.strictEqual(parsed?.definitionOverrides[0].expression, 'MC_Nat');
    });

    test('Round-trips spec options through serialization', () => {
        const state: ModelEditorState = {
            specName: 'Spec',
            specPath: path.join('/tmp', 'Spec.tla'),
            modelName: 'MCSpec',
            behavior: { kind: 'initNext', init: 'Init', next: 'Next' },
            checkDeadlock: true,
            constants: [],
            invariants: [],
            properties: [],
            stateConstraint: 'Len(q) < 5',
            actionConstraint: 'ActionOK',
            definitionOverrides: [{ name: 'Nat', expression: '0..10' }],
            additionalDefinitions: 'MaxVal == 10'
        };

        const files = serializeModelEditorState(state);
        const parsed = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            files.tlaContent, files.cfgContent
        );
        assert.ok(parsed);
        assert.strictEqual(parsed?.stateConstraint, 'Len(q) < 5');
        assert.strictEqual(parsed?.actionConstraint, 'ActionOK');
        assert.deepStrictEqual(parsed?.definitionOverrides,
            state.definitionOverrides);
        assert.strictEqual(parsed?.additionalDefinitions, 'MaxVal == 10');
    });
});
