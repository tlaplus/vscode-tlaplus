import * as assert from 'assert';
import * as path from 'path';
import {
    buildModelEditorPaths,
    discoverSpecInfo,
    parseModelEditorState,
    serializeModelEditorState,
    ModelEditorState
} from '../../../src/model/modelEditorFiles';

suite('Model editor files', () => {
    const base: ModelEditorState = {
        specName: 'Spec', specPath: path.join('/tmp', 'Spec.tla'),
        modelName: 'MCSpec',
        behavior: { kind: 'initNext', init: 'Init', next: 'Next' },
        checkDeadlock: true, constants: [], invariants: [], properties: [],
        stateConstraint: '', actionConstraint: '',
        definitionOverrides: [], additionalDefinitions: '',
        symmetryConstants: [], viewExpression: '', alias: '', postCondition: ''
    };

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
    });

    test('Serializes editor state into TLC files', () => {
        const state: ModelEditorState = {
            ...base,
            checkDeadlock: false,
            constants: [
                { name: 'N', kind: 'ordinary', value: '3' },
                { name: 'Nodes', kind: 'setModelValues', value: 'a, b' }
            ],
            invariants: ['TypeOK'],
            properties: ['Liveness']
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
            ...base,
            behavior: { kind: 'temporal', temporal: 'Spec' },
            constants: [{ name: 'Node', kind: 'modelValue', value: 'node_a' }],
            invariants: ['TypeOK']
        };
        const files = serializeModelEditorState(state);
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'), files.tlaContent, files.cfgContent
        );
        assert.ok(result);
        const parsed = result!.state;
        assert.strictEqual(parsed.behavior.kind, 'temporal');
        assert.strictEqual(parsed.behavior.temporal, 'Spec');
        assert.deepStrictEqual(parsed.constants, state.constants);
        assert.deepStrictEqual(parsed.invariants, state.invariants);
    });

    test('Parses simple existing cfg content without editor metadata', () => {
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            'CONSTANTS\n    greeting = "Hello"\n    Node <- node_a\nINIT Init\nNEXT Next\nINVARIANT TypeOK\nPROPERTY Liveness'
        );
        assert.ok(result);
        const parsed = result!.state;
        assert.strictEqual(parsed.behavior.kind, 'initNext');
        assert.strictEqual(parsed.constants[0].name, 'greeting');
        assert.strictEqual(parsed.constants[1].kind, 'modelValue');
        assert.deepStrictEqual(parsed.invariants, ['TypeOK']);
        assert.deepStrictEqual(parsed.properties, ['Liveness']);
    });

    test('Parses plural invariants/properties and constants across blank lines', () => {
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            'CONSTANTS\n  a1 = a1  a2 = a2\n\n  a3 = a3\nINVARIANTS TypeOK Safety\nPROPERTIES Liveness Fairness'
        );
        assert.ok(result);
        const parsed = result!.state;
        assert.deepStrictEqual(parsed.constants.map((c) => c.name), ['a1', 'a2', 'a3']);
        assert.deepStrictEqual(parsed.invariants, ['TypeOK', 'Safety']);
        assert.deepStrictEqual(parsed.properties, ['Liveness', 'Fairness']);
    });

    test('Discovers parameterized constants without splitting on inner commas', () => {
        const discovered = discoverSpecInfo('CONSTANTS N(_, _), M, P(x)\nFoo == 1');
        assert.deepStrictEqual(discovered.constants, ['M', 'N(_, _)', 'P(x)']);
    });

    test('Serializes state constraint and action constraint', () => {
        const state: ModelEditorState = {
            ...base,
            stateConstraint: 'StateLimit', actionConstraint: 'ActionLimit'
        };
        const files = serializeModelEditorState(state);
        assert.match(files.cfgContent, /CONSTRAINT StateLimit/);
        assert.match(files.cfgContent, /ACTION_CONSTRAINT ActionLimit/);
    });

    test('Serializes definition overrides into cfg and tla', () => {
        const state: ModelEditorState = {
            ...base,
            definitionOverrides: [{ name: 'Nat', expression: '0..10' }]
        };
        const files = serializeModelEditorState(state);
        assert.match(files.cfgContent, /CONSTANT Nat <- MC_Nat/);
        assert.match(files.tlaContent, /MC_Nat == 0\.\.10/);
    });

    test('Serializes additional definitions into tla', () => {
        const state: ModelEditorState = {
            ...base,
            behavior: { kind: 'none' },
            additionalDefinitions: 'MaxVal == 10\nASSUME MaxVal > 0'
        };
        const files = serializeModelEditorState(state);
        assert.match(files.tlaContent, /MaxVal == 10/);
        assert.match(files.tlaContent, /ASSUME MaxVal > 0/);
        const eqIdx = files.tlaContent.indexOf('====');
        const defIdx = files.tlaContent.indexOf('MaxVal == 10');
        assert.ok(defIdx < eqIdx, 'Additional definitions must come before ====');
    });

    test('Parses constraint and action constraint from raw cfg', () => {
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            'INIT Init\nNEXT Next\nCONSTRAINT StateLimit\nACTION_CONSTRAINT ActionLimit'
        );
        assert.ok(result);
        assert.strictEqual(result!.state.stateConstraint, 'StateLimit');
        assert.strictEqual(result!.state.actionConstraint, 'ActionLimit');
    });

    test('Parses definition overrides from raw cfg', () => {
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            'INIT Init\nNEXT Next\nCONSTANT Nat <- MC_Nat'
        );
        assert.ok(result);
        assert.strictEqual(result!.state.definitionOverrides.length, 1);
        assert.strictEqual(result!.state.definitionOverrides[0].name, 'Nat');
    });

    test('Round-trips spec options through serialization', () => {
        const state: ModelEditorState = {
            ...base,
            stateConstraint: 'Len(q) < 5', actionConstraint: 'ActionOK',
            definitionOverrides: [{ name: 'Nat', expression: '0..10' }],
            additionalDefinitions: 'MaxVal == 10'
        };
        const files = serializeModelEditorState(state);
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'), files.tlaContent, files.cfgContent
        );
        assert.ok(result);
        const parsed = result!.state;
        assert.strictEqual(parsed.stateConstraint, 'Len(q) < 5');
        assert.strictEqual(parsed.actionConstraint, 'ActionOK');
        assert.deepStrictEqual(parsed.definitionOverrides, state.definitionOverrides);
        assert.strictEqual(parsed.additionalDefinitions, 'MaxVal == 10');
    });

    test('Round-trips TLC options through serialization', () => {
        const tlcOpts = {
            checkingMode: 'simulate' as const, workers: 4, dfidDepth: 50,
            simulateTraces: 100, simulateSeed: '42', fpBits: 2,
            enableProfiling: true
        };
        const files = serializeModelEditorState(base, tlcOpts);
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'), files.tlaContent, files.cfgContent
        );
        assert.ok(result);
        assert.ok(result!.tlcOptions);
        assert.strictEqual(result!.tlcOptions!.checkingMode, 'simulate');
        assert.strictEqual(result!.tlcOptions!.workers, 4);
        assert.strictEqual(result!.tlcOptions!.simulateTraces, 100);
    });

    test('Serializes SYMMETRY into cfg and tla', () => {
        const state: ModelEditorState = {
            ...base,
            constants: [{ name: 'Nodes', kind: 'setModelValues', value: 'a, b' }],
            symmetryConstants: ['Nodes']
        };
        const files = serializeModelEditorState(state);
        assert.match(files.cfgContent, /SYMMETRY MC_symm_Nodes/);
        assert.match(files.tlaContent, /MC_symm_Nodes == Permutations\(Nodes\)/);
    });

    test('Serializes VIEW, ALIAS, POSTCONDITION into cfg', () => {
        const state: ModelEditorState = {
            ...base,
            viewExpression: '<<pc, stack>>',
            alias: 'MyAlias',
            postCondition: 'PostOp'
        };
        const files = serializeModelEditorState(state);
        assert.match(files.cfgContent, /VIEW <<pc, stack>>/);
        assert.match(files.cfgContent, /ALIAS MyAlias/);
        assert.match(files.cfgContent, /POSTCONDITION PostOp/);
    });

    test('Parses VIEW, ALIAS, POSTCONDITION, SYMMETRY from raw cfg', () => {
        const result = parseModelEditorState(
            path.join('/tmp', 'Spec.tla'),
            '---- MODULE Spec ----\n====',
            'INIT Init\nNEXT Next\nVIEW <<pc>>\nALIAS A\nPOSTCONDITION P\nSYMMETRY Sym1'
        );
        assert.ok(result);
        assert.strictEqual(result!.state.viewExpression, '<<pc>>');
        assert.strictEqual(result!.state.alias, 'A');
        assert.strictEqual(result!.state.postCondition, 'P');
        assert.deepStrictEqual(result!.state.symmetryConstants, ['Sym1']);
    });
});
