import * as React from 'react';
import { TlapsProofObligationState, TlapsProofStepDetails } from '../../../model/tlaps.ts';
import { VSCodeLink } from '@vscode/webview-ui-toolkit/react/index';
import { vscodeClient } from '../vscode_client.ts';
import { Location } from 'vscode-languageclient';
import './index.css';

interface ObligationI { details: TlapsProofStepDetails; obligation: TlapsProofObligationState }
export const Obligation = React.memo(({ details, obligation }: ObligationI) => {
    const location = { uri: details.location.uri, range: obligation.range } as Location;
    const showLocation = () => vscodeClient.showLocation(location);
    const results = obligation.results && obligation.results.length > 0
        ? <ul>{obligation.results.map(r => {
            const reason = r.reason ? <span className='comment'>({r.reason})</span> : null;
            const meth = r.meth ? <span className='comment'>[{r.meth}]</span> : null;
            return (<li>{r.prover}{meth}:<br />{r.status}{reason}</li>);
        })}</ul>
        : <p>Not checked yet.</p>;
    return (
        <section className={ obligation.role === 'main' ? 'role-main' : 'role-other'}>
            <div>
                <div>
                    <b>Obligation {obligation.role === 'main' ? null : <span>[{obligation.role}]</span>} at</b>&nbsp;
                    <VSCodeLink onClick={showLocation}>
                        {obligation.range.start.line + 1}:{obligation.range.start.character + 1}
                    </VSCodeLink>
                </div>
                {results}
                <pre>{obligation.normalized}</pre>
            </div>
        </section>
    );
});
