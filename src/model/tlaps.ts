import { Location } from 'vscode-languageclient/node';

export interface TlapsProofObligationResult {
    prover: string;
    meth: string;
    status: string;
    duration: number;
    obligation: string | null; // Non-null, if prover failed.
}

export interface TlapsProofObligationState {
    location: Location;
    obligation: string;
    results: TlapsProofObligationResult[];
}
