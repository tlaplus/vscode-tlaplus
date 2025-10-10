import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { TlapsConfigChanged, TlapsProofObligationState, TlapsProofStepDetails } from '../../model/tlaps.ts';
import { Obligation } from './obligation/index.tsx';
import { StepCounts } from './stepCounts/index.tsx';
import { VSCodeLink } from '../checkResultView/common';
import { vscodeClient } from './vscode_client.ts';
import { ProofStatusIcon } from './proofStatusIcon/index.tsx';
import '@vscode/codicons/dist/codicon.css';

interface CurrentProofStepViewAppI {
    config: TlapsConfigChanged | null,
    details: TlapsProofStepDetails | null
}
const CurrentProofStepViewApp = React.memo(({ config, details }: CurrentProofStepViewAppI) => {
    if (!config) {
        return (
            <React.StrictMode>
                <p>Initializing...</p>
            </React.StrictMode>
        );
    }

    if (!config.enabled) {
        return (
            <React.StrictMode>
                <p>This view is related to the TLA+ proof system.
                If you are focused on model checking with TLC or Apalache,
                which is typical for most TLA+ beginners, you can ignore this view.
                To hide it, simply right-click on the VSCode action bar and uncheck 'TLA+'.
                If you later want to use the TLA+ proof system, you can enable it
                by going to the VSCode settings and checking the appropriate TLA+
                integration <a href="vscode://settings/tlaplus.tlaps.enabled">options</a>.</p>
            </React.StrictMode>
        );
    }

    if (!details) {
        return (
            <React.StrictMode>
                <p>No proof step selected.</p>
            </React.StrictMode>
        );
    }

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
    const obsMain: TlapsProofObligationState[] = [];
    const obsOthers: TlapsProofObligationState[] = [];
    details.obligations.forEach(obl => {
        // We will show the main obligations before the other.
        if (obl.role === 'main') {
            obsMain.push(obl);
        } else {
            obsOthers.push(obl);
        }
    });
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
                {obsMain.map((obl, index) => <Obligation key={index} details={details} obligation={obl} />)}
                {obsOthers.map((obl, index) => <Obligation key={index} details={details} obligation={obl} />)}
            </section>
        </React.StrictMode>
    );
});

const root = createRoot(document.getElementById('root') as HTMLElement);

let tlapsProofStepDetails: TlapsProofStepDetails | null = null;
let tlapsConfigChanged: TlapsConfigChanged | null = null;

function render() {
    root.render(<CurrentProofStepViewApp config={tlapsConfigChanged} details={tlapsProofStepDetails} />);
}

window.addEventListener('message', event => {
    if (event.data.command === 'tlapsProofStepDetails') {
        tlapsProofStepDetails = event.data.details;
        render();
    } else if (event.data.command === 'tlapsConfigChanged') {
        tlapsConfigChanged = event.data.details;
        render();
    }
});

window.addEventListener('load', () => {
    vscodeClient.reportInitialized();
    render();
});
