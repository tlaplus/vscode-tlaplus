import * as React from 'react';
import { proofStateIcons } from '../vscode_client';
import './index.css';

interface ProofStatusIconI { proofStatus: string }
export const ProofStatusIcon = React.memo(({ proofStatus }: ProofStatusIconI) => {
    return (
        <img
            className='proof-state-icon'
            src={proofStateIcons[proofStatus]}
            alt={proofStatus}
            title={proofStatus}>
        </img>
    );
});
