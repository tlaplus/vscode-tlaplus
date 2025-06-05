import { WebviewApi } from 'vscode-webview';

/**
 * A utility wrapper around the acquireVsCodeApi() function that enables
 * message passing and state management between the webview and the extension.
 *
 * This should be called out once during the webview's initialization.
 * Afterward, exported function wrappers can be used to interact with the extension.
 */
class VSCodeApiWrapper {
    private readonly vsCodeApi: WebviewApi<unknown> | undefined;

    constructor() {
        // Check if the acquireVsCodeApi function exists in the current development
        // context (i.e. VS Code development window or web browser)
        if (typeof acquireVsCodeApi === 'function') {
            this.vsCodeApi = acquireVsCodeApi();
        }
    }

    /**
     * Post a message (i.e. send arbitrary data) to the extension.
     *
     * @param message Arbitrary data (must be JSON serializable) to send to the extension
     */
    public postMessage(message: unknown) {
        if (this.vsCodeApi) {
            this.vsCodeApi.postMessage(message);
        }
    }

    /**
     * Get the persistent state stored for this webview.
     *
     * @return The current state or undefined if no state has been set
     */
    public getState(): unknown | undefined {
        if (this.vsCodeApi) {
            return this.vsCodeApi.getState();
        } else {
            const state = localStorage.getItem('vscodeState');
            return state ? JSON.parse(state) : undefined;
        }
    }

    /**
     * Set the persistent state stored for this webview.
     *
     * @param newState New persisted state. This must be a JSON serializable object.
     */
    public setState<T extends unknown | undefined>(newState: T): T {
        if (this.vsCodeApi) {
            return this.vsCodeApi.setState(newState);
        } else {
            localStorage.setItem('vscodeState', JSON.stringify(newState));
            return newState;
        }
    }
}

// Export singleton to prevent multiple invocations of acquireVsCodeApi
export const vscode = new VSCodeApiWrapper();