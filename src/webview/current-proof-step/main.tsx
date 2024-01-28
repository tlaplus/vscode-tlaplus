import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { TlapsProofStepDetails } from '../../model/tlaps.ts';
import { Obligation } from './obligation/index.tsx';
import { StepCounts } from './stepCounts/index.tsx';
import { VSCodeLink } from '@vscode/webview-ui-toolkit/react/index';
import { vscodeClient } from './vscode_client.ts';
import { ProofStatusIcon } from './proofStatusIcon/index.tsx';
import '@vscode/codicons/dist/codicon.css';

interface CurrentProofStepViewAppI { details: TlapsProofStepDetails | null }
const CurrentProofStepViewApp = React.memo(({ details }: CurrentProofStepViewAppI) => {
    if (details) {
        let subLabel = 'Steps: ';
        if (details.kind === 'module') {
            subLabel = 'Theorems: ';
        }
        const stepKind = (kind: string): string => {
            switch (kind) {
                case 'module': return 'Module';
                case 'struct': return 'Structured proof';
                case 'leaf': return 'Leaf proof step';
                default: return kind;
            }
        };
        return (
            <React.StrictMode>
                <section>
                    <div>
                        <b>{stepKind(details.kind)}</b>&nbsp;
                        <ProofStatusIcon proofStatus={details.status}></ProofStatusIcon>
                        &nbsp;at&nbsp;
                        <VSCodeLink onClick={() => vscodeClient.showLocation(details.location)}>
                            {details.location.uri.split(/\/|\\/).pop()}&nbsp;
                            {details.location.range.start.line + 1}:
                            {details.location.range.start.character + 1}
                        </VSCodeLink>
                    </div>
                    <StepCounts label={subLabel} counts={details.sub_count}></StepCounts>
                </section>
                <section>
                    {details.obligations.map((obl, index) =>
                        <Obligation key={index} details={details} obligation={obl} />
                    )}
                </section>
            </React.StrictMode>
        );
    } else {
        return (
            <React.StrictMode>
                <p>No proof step selected.</p>
            </React.StrictMode>
        );
    }
});

const root = createRoot(document.getElementById('root') as HTMLElement);

function render(details: TlapsProofStepDetails | null) {
    root.render(<CurrentProofStepViewApp details={details} />);
}

window.addEventListener('message', event => {
    if (event.data.command === 'tlapsProofStepDetails') {
        render(event.data.details as TlapsProofStepDetails | null);
    }
});

window.addEventListener('load', () => render(null));
