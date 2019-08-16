import * as vscode from 'vscode';

const dc = vscode.languages.createDiagnosticCollection('tlaplus');

/**
 * An expectation of set ot diagnostics for the given file path.
 */
export class Expectation {
    public readonly filePath: string;
    public readonly diagnostics: vscode.Diagnostic[];

    constructor(filePath: string, diagnostics: vscode.Diagnostic[]) {
        this.filePath = filePath;
        this.diagnostics = diagnostics;
    }
}

export function getTlaDiagnostics(): vscode.DiagnosticCollection {
    return dc;
}

export function range(fromLine: number, fromSymbol: number, toLine: number, toSymbol: number): vscode.Range {
    return new vscode.Range(
        new vscode.Position(fromLine, fromSymbol),
        new vscode.Position(toLine, toSymbol)
    );
}

/**
 * Creates an expectation of set ot diagnostics for the given file path.
 */
export function expectDiag(filePath: string, diagnostics: vscode.Diagnostic[]): Expectation {
    return new Expectation(filePath, diagnostics);
}

/**
 * Creates a diagnostic with the Error severity.
 */
export function diagError(range: vscode.Range, message: string): vscode.Diagnostic {
    return new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Error);
}
