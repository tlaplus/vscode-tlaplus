import * as vscode from 'vscode';
import {
    SemanticAuthority,
    SemanticFreshness,
    SemanticSnapshot,
    SemanticSource,
    TlaDocumentInfo,
} from '../model/documentInfo';

export interface SemanticSnapshotInput {
    documentInfo: TlaDocumentInfo;
    source: SemanticSource;
    freshness: SemanticFreshness;
    authority: SemanticAuthority;
    documentVersion?: number;
    includeExtendedModules?: boolean;
}

export class SemanticService {
    private readonly snapshots = new Map<string, SemanticSnapshot>();

    getSnapshot(uri: vscode.Uri): SemanticSnapshot | undefined {
        return this.snapshots.get(uri.toString());
    }

    getOrCreateSnapshot(uri: vscode.Uri): SemanticSnapshot {
        const existing = this.getSnapshot(uri);
        if (existing) {
            return existing;
        }
        const snapshot = new SemanticSnapshot();
        this.snapshots.set(uri.toString(), snapshot);
        return snapshot;
    }

    getDocumentInfo(uri: vscode.Uri): TlaDocumentInfo {
        return this.getOrCreateSnapshot(uri).documentInfo;
    }

    updateSnapshot(uri: vscode.Uri, input: SemanticSnapshotInput): SemanticSnapshot {
        const snapshot = new SemanticSnapshot(
            input.documentInfo,
            input.source,
            input.freshness,
            input.authority,
            input.documentVersion,
            input.includeExtendedModules ?? false
        );
        this.snapshots.set(uri.toString(), snapshot);
        return snapshot;
    }

    clear(uri?: vscode.Uri): void {
        if (uri) {
            this.snapshots.delete(uri.toString());
            return;
        }
        this.snapshots.clear();
    }
}
