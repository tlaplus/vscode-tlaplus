interface IVsCodeApi {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    postMessage(msg: any): void;
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    setState(state: any): void;
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    getState(): any;
}

// This special function talks to vscode from a web panel
declare function acquireVsCodeApi(): IVsCodeApi;

const vsCodeApi = acquireVsCodeApi();

class VSCodeWrapper {

    public openFile(filePath: string, location: unknown) {
        vsCodeApi.postMessage({
            command: 'openFile',
            filePath,
            location
        });
    }

    public stopProcess() {
        vsCodeApi.postMessage({
            command: 'stop'
        });
    }

    public checkAgain() {
        vsCodeApi.postMessage({
            command: 'runAgain'
        });
    }

    public showTlcOutput() {
        vsCodeApi.postMessage({
            command: 'showTlcOutput'
        });
    }

    public showVariableValue(id: number) {
        vsCodeApi.postMessage({
            command: 'showVariableValue',
            valueId: id
        });
    }

    public showInfoMessage(text: string) {
        vsCodeApi.postMessage({
            command: 'showInfoMessage',
            text: text
        });
    }

    public setState<T extends unknown | undefined>(newState: T) {
        return vsCodeApi.setState(newState);
    }

    public getState(): unknown {
        return vsCodeApi.getState();
    }
}

export const vscode = new VSCodeWrapper();
