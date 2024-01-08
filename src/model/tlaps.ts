import { Location } from 'vscode-languageclient/node';

export interface TlapsProofObligationResult {
    prover: string;
    meth: string;
    status: string;
    reason: string | null;
    obligation: string | null; // Non-null, if prover failed.
}

export interface TlapsProofObligationState {
    location: Location;
    obligation: string;
    results: TlapsProofObligationResult[];
}
