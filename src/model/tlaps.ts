import { Location, Range } from 'vscode-languageclient/node';

export interface TlapsProofObligationResult {
    prover: string;
    meth: string;
    status: string;
    reason: string | null;
    obligation: string | null; // Non-null, if prover failed.
}

export interface TlapsProofObligationState {
    range: Range;
    normalized: string;
    results: TlapsProofObligationResult[];
}

export interface TlapsProofStepDetails {
    kind: string;
    location: Location;
    obligations: TlapsProofObligationState[];
}
