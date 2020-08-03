import * as vscode from 'vscode';
import * as assert from 'assert';
import { loc, pos } from '../shortcuts';
import { TlaDocumentInfos } from '../../../src/model/documentInfo';

export function assertSymbolClass(
    labels: string[],
    expKind: vscode.CompletionItemKind,
    list: vscode.CompletionList
): number {
    labels.forEach((label) => {
        assertCompletion(label, expKind, list);
    });
    return labels.length;
}

export function assertCompletion(
    label: string,
    expectKind: vscode.CompletionItemKind,
    list: vscode.CompletionList
): void {
    const comp = list.items.find((c) => c.label === label);
    if (comp) {
        assert.equal(comp.kind, expectKind);
    } else {
        assert.fail(`Completion ${label} not found`);
    }
}

export function createTestDocInfos(docUri: vscode.Uri): TlaDocumentInfos {
    const symbolsList = [];
    symbolsList.push(
        new vscode.SymbolInformation('Foo', vscode.SymbolKind.Field, 'test', loc(docUri, pos(0, 0)))
    );
    const docInfos = new TlaDocumentInfos();
    docInfos.get(docUri).symbols = symbolsList;
    return docInfos;
}
