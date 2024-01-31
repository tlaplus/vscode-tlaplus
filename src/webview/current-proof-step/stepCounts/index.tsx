import * as React from 'react';
import { CountByStepStatus } from '../../../model/tlaps';
import { ProofStatusIcon } from '../proofStatusIcon';

interface StepCountsI { label: string; counts: CountByStepStatus }
export const StepCounts = React.memo(({ label, counts }: StepCountsI) => {
    const states = [
        'proved',
        'failed',
        'missing',
        'omitted',
        'pending',
        'progress',
    ];
    if (states.every(state => counts[state] === 0)) {
        return null;
    }
    const f = (name: string, value: number) => {
        if (value === 0) {
            return null;
        }
        return (<span><ProofStatusIcon proofStatus={name}></ProofStatusIcon> {value} </span>);
    };
    return (
        <span>
            <b>{label}</b> {states.map((state) => f(state, counts[state]))}
        </span>
    );
});
