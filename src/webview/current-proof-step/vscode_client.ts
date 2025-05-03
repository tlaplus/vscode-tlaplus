import { Location } from 'vscode-languageclient';
import { vsCodeApi } from '../common/vscode_api';
import { ProofStateIcons } from '../../tlaps';

// These are set on the initialization, inline in the HTML template.
declare const webviewProofStateNames: string[];
declare const webviewProofStateIcons: ProofStateIcons;

export const proofStateNames = webviewProofStateNames;
export const proofStateIcons = webviewProofStateIcons;

class VSCodeClient {

    public reportInitialized() {
        vsCodeApi.postMessage({
            command: 'initialized'
        });
    }

    public showLocation(location: Location) {
        vsCodeApi.postMessage({
            command: 'showLocation',
            location
        });
    }
}

export const vscodeClient = new VSCodeClient();
