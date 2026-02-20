import * as assert from 'assert';
import { TlaDocumentInfo } from '../../../src/model/documentInfo';

suite('TlaDocumentInfo', () => {
    test('Returns module dependency graph from XML data', () => {
        const sourceGraph = new Map<string, string[]>([
            ['MCSpec', ['Spec', 'TLC']],
            ['Spec', ['Naturals']]
        ]);
        const info = new TlaDocumentInfo(
            undefined,
            undefined,
            [],
            [],
            {
                rootModuleName: 'MCSpec',
                extendsGraph: sourceGraph
            }
        );

        assert.strictEqual(info.getRootModuleName(), 'MCSpec');
        assert.deepStrictEqual(info.getExtendedModules('MCSpec'), ['Spec', 'TLC']);
        assert.deepStrictEqual(info.getExtendedModules('Spec'), ['Naturals']);
        assert.deepStrictEqual(info.getExtendedModules('MissingModule'), []);
    });

    test('Returns defensive copies for module dependency data', () => {
        const sourceGraph = new Map<string, string[]>([
            ['MCSpec', ['Spec']]
        ]);
        const info = new TlaDocumentInfo(
            undefined,
            undefined,
            [],
            [],
            {
                rootModuleName: 'MCSpec',
                extendsGraph: sourceGraph
            }
        );

        sourceGraph.get('MCSpec')!.push('TLC');
        assert.deepStrictEqual(info.getExtendedModules('MCSpec'), ['Spec']);

        const graphCopy = info.getExtendsGraph();
        graphCopy.get('MCSpec')!.push('Naturals');
        graphCopy.set('Other', ['Module']);

        assert.deepStrictEqual(info.getExtendedModules('MCSpec'), ['Spec']);
        assert.deepStrictEqual(info.getExtendedModules('Other'), []);
    });
});
