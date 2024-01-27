import { Location } from 'vscode-languageclient';
import { vsCodeApi } from '../common/vscode_api';


class VSCodeClient {

    public showLocation(location: Location) {
        vsCodeApi.postMessage({
            command: 'showLocation',
            location
        });
    }
}

export const vscodeClient = new VSCodeClient();
