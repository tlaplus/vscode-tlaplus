import * as React from 'react';
import './index.css';
import { proofStateIcons } from '../vscode_client';

interface ProofStatusIconI { proofStatus: string }
export const ProofStatusIcon = React.memo(({ proofStatus }: ProofStatusIconI) => {
    const style = {
        height: '14px',
        width: '14px',
        'vertical-align': '-15%',
    };
    return (
        <img
            style={style}
            src={proofStateIcons[proofStatus]}
            alt={proofStatus}
            title={proofStatus}>
        </img>
    );
});
