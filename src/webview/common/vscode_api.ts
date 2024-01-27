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

export const vsCodeApi = acquireVsCodeApi();
