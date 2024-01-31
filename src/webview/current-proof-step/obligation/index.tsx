import * as React from 'react';
import { TlapsProofObligationState, TlapsProofStepDetails } from '../../../model/tlaps.ts';
import { VSCodeLink } from '@vscode/webview-ui-toolkit/react/index';
import { vscodeClient } from '../vscode_client.ts';
import { Location } from 'vscode-languageclient';
import { ProofStatusIcon } from '../proofStatusIcon/index.tsx';
import './index.css';

interface ObligationI { details: TlapsProofStepDetails; obligation: TlapsProofObligationState }
export const Obligation = React.memo(({ details, obligation }: ObligationI) => {
    if (obligation.role === 'aux' && obligation.status !== 'failed') {
        // Do not show the auxiliary obligations, unless they are failed.
        return null;
    }
    const location = { uri: details.location.uri, range: obligation.range } as Location;
    const showLocation = () => vscodeClient.showLocation(location);
    const results = obligation.results && obligation.results.length > 0
        ? <ul className='prover-list'>{obligation.results.map(r => {
            const reason = r.reason ? (<>:<br /><span className='comment'>({r.reason})</span></>) : null;
            const meth = r.meth ? <span className='comment'>[{r.meth}]</span> : null;
            return (
                <li>
                    <ProofStatusIcon proofStatus={r.status}></ProofStatusIcon>&nbsp;
                    {r.prover}{meth}{reason}
                </li>
            );
        })}</ul>
        : null;
    return (
        <section className={obligation.role === 'main' ? 'role-main' : 'role-other'}>
            <div>
                <div>
                    <b>
                        Obligation
                        {obligation.role === 'main' ? null : <span>[{obligation.role}]</span>}&nbsp;
                        <ProofStatusIcon proofStatus={obligation.status}></ProofStatusIcon>
                    </b>&nbsp;at&nbsp;
                    <VSCodeLink onClick={showLocation}>
                        {obligation.range.start.line + 1}:{obligation.range.start.character + 1}
                    </VSCodeLink>
                </div>
                {results}
                <pre className='obl-text'>{obligation.normalized}</pre>
            </div>
        </section>
    );
});
