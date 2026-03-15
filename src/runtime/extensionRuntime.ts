import * as vscode from 'vscode';
import { DiagnosticsProjector } from '../services/diagnosticsProjector';
import { ParseService } from '../services/parseService';
import { CheckService } from '../services/checkService';
import { SemanticService } from '../services/semanticService';

export interface ExtensionRuntime {
    diagnosticsProjector: DiagnosticsProjector;
    parseService: ParseService;
    checkService: CheckService;
    semanticService: SemanticService;
}

export function createExtensionRuntime(diagnosticCollection: vscode.DiagnosticCollection): ExtensionRuntime {
    return {
        diagnosticsProjector: new DiagnosticsProjector(diagnosticCollection),
        parseService: new ParseService(),
        checkService: new CheckService(),
        semanticService: new SemanticService(),
    };
}
