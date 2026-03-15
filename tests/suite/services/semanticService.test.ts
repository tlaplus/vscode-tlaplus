import * as assert from 'assert';
import * as vscode from 'vscode';
import { TlaDocumentInfo } from '../../../src/model/documentInfo';
import { SemanticService } from '../../../src/services/semanticService';

suite('SemanticService', () => {
    test('stores semantic snapshot metadata and document info', () => {
        const service = new SemanticService();
        const uri = vscode.Uri.file('/tmp/Spec.tla');
        const documentInfo = new TlaDocumentInfo();

        service.updateSnapshot(uri, {
            documentInfo,
            source: 'merged',
            freshness: 'current',
            authority: 'authoritative',
            documentVersion: 7,
            includeExtendedModules: true,
        });

        const snapshot = service.getSnapshot(uri);
        assert.ok(snapshot);
        assert.strictEqual(snapshot?.documentInfo, documentInfo);
        assert.strictEqual(snapshot?.source, 'merged');
        assert.strictEqual(snapshot?.freshness, 'current');
        assert.strictEqual(snapshot?.authority, 'authoritative');
        assert.strictEqual(snapshot?.documentVersion, 7);
        assert.strictEqual(snapshot?.includeExtendedModules, true);
        assert.strictEqual(service.getDocumentInfo(uri), documentInfo);
    });

    test('clear removes one snapshot or all snapshots', () => {
        const service = new SemanticService();
        const uriOne = vscode.Uri.file('/tmp/One.tla');
        const uriTwo = vscode.Uri.file('/tmp/Two.tla');

        service.updateSnapshot(uriOne, {
            documentInfo: new TlaDocumentInfo(),
            source: 'heuristic',
            freshness: 'partial',
            authority: 'heuristic',
        });
        service.updateSnapshot(uriTwo, {
            documentInfo: new TlaDocumentInfo(),
            source: 'sany',
            freshness: 'current',
            authority: 'authoritative',
        });

        service.clear(uriOne);
        assert.strictEqual(service.getSnapshot(uriOne), undefined);
        assert.ok(service.getSnapshot(uriTwo));

        service.clear();
        assert.strictEqual(service.getSnapshot(uriTwo), undefined);
    });
});
