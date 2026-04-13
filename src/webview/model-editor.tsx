import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { vsCodeApi } from './common/vscode_api';
import type {
    DiscoveredSpecInfo,
    ModelEditorState,
    TlcOptionsState
} from '../model/modelEditorFiles';
import { S } from './model-editor/styles';
import { isAnyDirty } from './model-editor/dirty';
import type { TabId } from './model-editor/dirty';
import { TabBar, ModelNameEditor } from './model-editor/components';
import { OverviewTab } from './model-editor/OverviewTab';
import { SpecOptionsTab } from './model-editor/SpecOptionsTab';
import { TlcOptionsTab } from './model-editor/TlcOptionsTab';


interface ModelEditorPanelData {
    state: ModelEditorState;
    discovered: DiscoveredSpecInfo;
    tlcOptions?: TlcOptionsState;
}


function App() {
    const persisted = vsCodeApi.getState() as
        ModelEditorPanelData | undefined;
    const [data, setData] = React.useState<
        ModelEditorPanelData | undefined
    >(persisted);
    const [savedState, setSavedState] = React.useState<
        ModelEditorState | undefined
    >(persisted?.state
        ? JSON.parse(JSON.stringify(persisted.state))
        : undefined
    );
    const [error, setError] = React.useState('');
    const [activeTab, setActiveTab] = React.useState<TabId>('overview');
    const defaultTlcOpts: TlcOptionsState = {
        checkingMode: 'bfs', workers: 0, dfidDepth: 100,
        simulateTraces: 0, simulateSeed: '', fpBits: 1,
        enableProfiling: false
    };
    const [tlcOptions, setTlcOptions] = React.useState<TlcOptionsState>(
        persisted?.tlcOptions ?? defaultTlcOpts
    );
    const [savedTlcOptions, setSavedTlcOptions] = React.useState<
        TlcOptionsState
    >(persisted?.tlcOptions
        ? JSON.parse(JSON.stringify(persisted.tlcOptions))
        : defaultTlcOpts
    );

    React.useEffect(() => {
        vsCodeApi.postMessage({ command: 'ready' });
        const listener = (event: MessageEvent<{
            type?: string;
            data?: ModelEditorPanelData;
            discovered?: DiscoveredSpecInfo;
            message?: string;
        }>) => {
            if (event.data?.type === 'init' && event.data.data) {
                const d = event.data.data;
                setData(d);
                setSavedState(
                    JSON.parse(JSON.stringify(d.state))
                );
                if (d.tlcOptions) {
                    setTlcOptions(d.tlcOptions);
                    setSavedTlcOptions(
                        JSON.parse(JSON.stringify(d.tlcOptions))
                    );
                }
                vsCodeApi.setState(d);
            } else if (event.data?.type === 'saved') {
                setError('');
                setData((prev) => {
                    if (prev) {
                        setSavedState(JSON.parse(
                            JSON.stringify(prev.state)
                        ));
                        vsCodeApi.setState(prev);
                    }
                    return prev;
                });
                setSavedTlcOptions(
                    JSON.parse(JSON.stringify(tlcOptions))
                );
            } else if (event.data?.type === 'error') {
                setError(event.data.message ?? 'Error.');
            } else if (
                event.data?.type === 'specUpdated'
                && event.data.discovered
            ) {
                const disc = event.data.discovered;
                setData((prev) => {
                    if (!prev) { return prev; }
                    // Merge new constants from spec
                    const merged = disc.constants.map((name) => {
                        const existing = prev.state.constants.find(
                            (c) => c.name === name
                        );
                        return existing ?? {
                            name,
                            kind: 'ordinary' as const,
                            value: ''
                        };
                    });
                    const next = {
                        ...prev,
                        discovered: disc,
                        state: {
                            ...prev.state, constants: merged
                        }
                    };
                    vsCodeApi.setState(next);
                    return next;
                });
            }
        };
        window.addEventListener('message', listener);
        return () => window.removeEventListener('message', listener);
    }, []);

    const updateState = React.useCallback(
        (fn: (s: ModelEditorState) => ModelEditorState) => {
            setData((prev) => {
                if (!prev) { return prev; }
                const next = {
                    ...prev, state: fn(prev.state)
                };
                vsCodeApi.setState(next);
                return next;
            });
        }, []
    );

    const revertFields = React.useCallback(
        (fn: (saved: ModelEditorState) => Partial<ModelEditorState>) => {
            if (!savedState) { return; }
            updateState((prev) => ({ ...prev, ...fn(savedState) }));
        }, [savedState, updateState]
    );

    if (!data || !savedState) {
        return <div style={S.page}>Loading model editor...</div>;
    }

    const { state, discovered } = data;
    const dirty = isAnyDirty(
        state, savedState, tlcOptions, savedTlcOptions
    );

    const saveModel = () => {
        vsCodeApi.postMessage({
            command: 'saveModel', state, tlcOptions
        });
    };

    const saveAndRun = () => {
        vsCodeApi.postMessage({
            command: 'saveAndRun', state, tlcOptions
        });
    };

    const openFile = (pathOrKind: string) => {
        vsCodeApi.postMessage({
            command: 'openFile',
            path: pathOrKind,
            modelName: state.modelName
        });
    };

    return (
        <div style={S.page}>
            <h1 style={S.heading}>TLA+ Model Editor</h1>

            <section style={S.section}>
                <div style={S.headerRow}>
                    <div>
                        <strong>Spec:</strong>{' '}
                        <a
                            style={S.fileLink}
                            href="#"
                            onClick={(e) => {
                                e.preventDefault();
                                openFile(state.specPath);
                            }}
                        >{state.specName}</a>
                        <ModelNameEditor
                            modelName={state.modelName}
                            onChange={(name) => updateState((prev) => ({
                                ...prev, modelName: name
                            }))}
                            onOpenFile={openFile}
                        />
                    </div>
                    <div style={S.buttonGroup}>
                        <button
                            style={{
                                ...S.button,
                                ...(dirty ? {} : S.buttonDisabled)
                            }}
                            onClick={saveModel}
                            disabled={!dirty}
                        >Save Model Files</button>
                        <button
                            style={S.buttonPrimary}
                            onClick={saveAndRun}
                        >{dirty ? 'Save & Run MC' : 'Run MC'}</button>
                    </div>
                </div>
                {error && (
                    <div style={S.errorText}>{error}</div>
                )}
            </section>

            <TabBar
                active={activeTab}
                onChange={setActiveTab}
                current={state}
                saved={savedState}
                currentTlc={tlcOptions}
                savedTlc={savedTlcOptions}
            />

            {activeTab === 'overview' && (
                <OverviewTab
                    state={state}
                    saved={savedState}
                    discovered={discovered}
                    update={updateState}
                    revert={revertFields}
                />
            )}
            {activeTab === 'specOptions' && (
                <SpecOptionsTab
                    state={state}
                    saved={savedState}
                    update={updateState}
                    revert={revertFields}
                />
            )}
            {activeTab === 'tlcOptions' && (
                <TlcOptionsTab
                    opts={tlcOptions}
                    onChange={(fn) => setTlcOptions(fn)}
                />
            )}
        </div>
    );
}


createRoot(
    document.getElementById('root') as HTMLElement
).render(<App />);
