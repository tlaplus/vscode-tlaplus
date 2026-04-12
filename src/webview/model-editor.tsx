import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { vsCodeApi } from './common/vscode_api';
import type {
    ConstantAssignmentKind,
    DiscoveredSpecInfo,
    ModelEditorState
} from '../model/modelEditorFiles';

// ── Types ─────────────────────────────────────────────────────────

type TabId = 'overview' | 'specOptions' | 'tlcOptions';

interface ModelEditorPanelData {
    state: ModelEditorState;
    discovered: DiscoveredSpecInfo;
    unsupportedDirectives: string[];
}

// ── Dirty-tracking helpers ──────────────────────────────────────

function deepEqual(a: unknown, b: unknown): boolean {
    return JSON.stringify(a) === JSON.stringify(b);
}

function isTabDirty(
    tab: TabId,
    current: ModelEditorState,
    saved: ModelEditorState
): boolean {
    if (tab === 'overview') {
        return !deepEqual(current.behavior, saved.behavior)
            || current.checkDeadlock !== saved.checkDeadlock
            || !deepEqual(current.constants, saved.constants)
            || !deepEqual(current.invariants, saved.invariants)
            || !deepEqual(current.properties, saved.properties);
    }
    if (tab === 'specOptions') {
        return current.stateConstraint !== saved.stateConstraint
            || current.actionConstraint !== saved.actionConstraint
            || !deepEqual(
                current.definitionOverrides, saved.definitionOverrides
            )
            || current.additionalDefinitions
                !== saved.additionalDefinitions;
    }
    return false;
}

function isAnyDirty(
    current: ModelEditorState,
    saved: ModelEditorState
): boolean {
    return !deepEqual(current, saved);
}

// ── Tooltip texts ─────────────────────────────

/* eslint-disable max-len */
const TIPS = {
    behaviorSpec: 'Defines how your system behaves by specifying the initial states (Init) and how states can transition (Next).',
    mode: 'Init/Next is the most common. Temporal formula uses a single spec operator. No behavior spec evaluates constant expressions only.',
    deadlock: 'Checks that every reachable state has at least one successor state.',
    invariants: 'State predicates checked in every reachable state.',
    properties: 'Temporal formulas verified over the full behavior graph.',
    constants: 'Assign concrete values to each CONSTANT declared in the spec. Use Ordinary for expressions, Model value for uninterpreted identifiers, or Set of model values for finite sets.',
    stateConstraint: 'A TLA+ expression that must be TRUE for a state to be explored. Use this to bound the model, e.g. Len(queue) < 5. Does not affect correctness.',
    actionConstraint: 'A TLA+ expression over primed and unprimed variables. Only transitions where this is TRUE are explored.',
    defOverrides: 'Replace spec operators with model-specific definitions. For example, replace Nat with 0..10 to make an infinite set finite.',
    additionalDefs: 'Free-form TLA+ text added to the MC module. Use for helper operators, ASSUME statements, or definitions needed by constraints or overrides.',
    tlcOptions: 'Runtime options for the model checker: checking mode, parallelism, memory, and profiling. Passed as command-line arguments.',
};
/* eslint-enable max-len */

// ── Reusable components ───────────────────────

function InfoTip(props: { text: string }) {
    const [show, setShow] = React.useState(false);
    return (
        <span
            style={S.infoTipWrap}
            onMouseEnter={() => setShow(true)}
            onMouseLeave={() => setShow(false)}
        >
            <span style={S.infoTipIcon}>ⓘ</span>
            {show && (
                <span style={S.infoTipPopover}>{props.text}</span>
            )}
        </span>
    );
}

function TabBar(props: {
    active: TabId;
    onChange: (tab: TabId) => void;
    current: ModelEditorState;
    saved: ModelEditorState;
}) {
    const tabs: { id: TabId; label: string }[] = [
        { id: 'overview', label: 'Model Overview' },
        { id: 'specOptions', label: 'Spec Options' },
        { id: 'tlcOptions', label: 'TLC Options' },
    ];
    return (
        <div style={S.tabBar}>
            {tabs.map((tab) => {
                const dirty = isTabDirty(
                    tab.id, props.current, props.saved
                );
                const active = props.active === tab.id;
                return (
                    <div key={tab.id} style={S.tabWrap}>
                        <button
                            style={{
                                ...S.tab,
                                ...(active ? S.tabActiveText : {})
                            }}
                            onClick={() => props.onChange(tab.id)}
                        >
                            {tab.label}{dirty ? ' *' : ''}
                        </button>
                        <div style={active
                            ? S.tabIndicator
                            : S.tabIndicatorHidden}
                        />
                    </div>
                );
            })}
        </div>
    );
}

function DirtyField(props: {
    dirty: boolean;
    onUndo: () => void;
    children: React.ReactNode;
}) {
    return (
        <div style={{
            ...S.dirtyField,
            ...(props.dirty ? S.dirtyFieldHighlight : {})
        }}>
            {props.children}
            {props.dirty && (
                <button
                    style={S.undoButton}
                    onClick={props.onUndo}
                    title="Revert to saved value"
                >↩</button>
            )}
        </div>
    );
}

function TextField(props: {
    label: string;
    value: string;
    suggestions?: string[];
    placeholder?: string;
    onChange: (value: string) => void;
}) {
    const [focused, setFocused] = React.useState(false);
    const wrapRef = React.useRef<HTMLLabelElement>(null);

    const filtered = (props.suggestions ?? []).filter(
        (s) => s.toLowerCase().includes(
            props.value.toLowerCase()
        ) && s !== props.value
    );
    const showSuggestions = focused && filtered.length > 0;

    return (
        <label
            style={{ ...S.label, position: 'relative' }}
            ref={wrapRef}
        >
            {props.label}
            <input
                style={S.input}
                value={props.value}
                placeholder={props.placeholder}
                onChange={(e) => props.onChange(e.target.value)}
                onFocus={() => setFocused(true)}
                onBlur={() => setTimeout(
                    () => setFocused(false), 150
                )}
            />
            {showSuggestions && (
                <div style={S.suggestBox}>
                    {filtered.map((s) => (
                        <div
                            key={s}
                            style={S.suggestItem}
                            onMouseDown={(e) => {
                                e.preventDefault();
                                props.onChange(s);
                                setFocused(false);
                            }}
                        >{s}</div>
                    ))}
                </div>
            )}
        </label>
    );
}

function TextListField(props: {
    label: string;
    info?: string;
    values: string[];
    suggestions: string[];
    onChange: (values: string[]) => void;
}) {
    const value = props.values.join(', ');
    return (
        <div style={S.listField}>
            <label style={S.fieldLabel}>
                {props.label}:
                {props.info && <InfoTip text={props.info} />}
                <input
                    style={S.input}
                    value={value}
                    placeholder="Comma-separated operator names"
                    onChange={(e) => props.onChange(
                        e.target.value.split(',')
                            .map((s) => s.trim())
                            .filter((s) => s.length > 0)
                    )}
                />
            </label>
            {props.suggestions.length > 0 && (
                <div style={S.suggestionRow}>
                    {props.suggestions.slice(0, 8).map((s) => (
                        <button
                            key={s}
                            style={S.chip}
                            onClick={() => {
                                if (!props.values.includes(s)) {
                                    props.onChange([...props.values, s]);
                                }
                            }}
                        >{s}</button>
                    ))}
                </div>
            )}
        </div>
    );
}

function InitNextFields(props: {
    init: string;
    next: string;
    discovered: DiscoveredSpecInfo;
    onChange: (init: string, next: string) => void;
}) {
    const [expanded, setExpanded] = React.useState(false);
    const hasDefaults = props.init && props.next;

    if (!expanded && hasDefaults) {
        return (
            <div style={S.initNextSummary}>
                <span style={S.smallText}>
                    Init = <strong>{props.init}</strong>,
                    Next = <strong>{props.next}</strong>
                </span>
                <button
                    style={S.linkButton}
                    onClick={() => setExpanded(true)}
                >change</button>
            </div>
        );
    }

    return (
        <div style={S.grid}>
            <TextField
                label="Init"
                value={props.init}
                suggestions={props.discovered.initCandidates}
                onChange={(v) => props.onChange(v, props.next)}
            />
            <TextField
                label="Next"
                value={props.next}
                suggestions={props.discovered.nextCandidates}
                onChange={(v) => props.onChange(props.init, v)}
            />
        </div>
    );
}

function TextArea(props: {
    label: string;
    value: string;
    placeholder?: string;
    onChange: (value: string) => void;
}) {
    return (
        <label style={S.label}>
            {props.label}
            <textarea
                style={{ ...S.input, minHeight: '80px', resize: 'vertical' } as React.CSSProperties}
                value={props.value}
                placeholder={props.placeholder}
                onChange={(e) => props.onChange(e.target.value)}
            />
        </label>
    );
}

// ── content Tab ────────────────────────

function OverviewTab(props: {
    state: ModelEditorState;
    saved: ModelEditorState;
    discovered: DiscoveredSpecInfo;
    update: (fn: (s: ModelEditorState) => ModelEditorState) => void;
    revert: (fn: (saved: ModelEditorState) => Partial<ModelEditorState>) => void;
}) {
    const { state: s, saved, discovered, update, revert } = props;

    return (<>
        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                BEHAVIOR SPEC
                <InfoTip text={TIPS.behaviorSpec} />
            </h2>
            <DirtyField
                dirty={!deepEqual(s.behavior, saved.behavior)}
                onUndo={() => revert((sv) => ({ behavior: sv.behavior }))}
            >
                <label style={S.fieldLabel}>
                    Mode:
                    <InfoTip text={TIPS.mode} />
                    <select
                        style={S.input}
                        value={s.behavior.kind}
                        onChange={(e) => update((prev) => ({
                            ...prev,
                            behavior: {
                                ...prev.behavior,
                                kind: e.target.value as
                                    ModelEditorState['behavior']['kind']
                            }
                        }))}
                    >
                        <option value="initNext">Init/Next</option>
                        <option value="temporal">Temporal formula</option>
                        <option value="none">No behavior spec</option>
                    </select>
                </label>

                {s.behavior.kind === 'initNext' && (
                    <InitNextFields
                        init={s.behavior.init ?? ''}
                        next={s.behavior.next ?? ''}
                        discovered={discovered}
                        onChange={(init, next) => update((prev) => ({
                            ...prev,
                            behavior: {
                                ...prev.behavior, init, next
                            }
                        }))}
                    />
                )}

                {s.behavior.kind === 'temporal' && (
                    <TextField
                        label="Specification operator"
                        value={s.behavior.temporal ?? ''}
                        suggestions={discovered.temporalCandidates}
                        onChange={(v) => update((prev) => ({
                            ...prev,
                            behavior: { ...prev.behavior, temporal: v }
                        }))}
                    />
                )}
            </DirtyField>
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>WHAT TO CHECK</h2>
            <DirtyField
                dirty={s.checkDeadlock !== saved.checkDeadlock}
                onUndo={() => revert((sv) => ({
                    checkDeadlock: sv.checkDeadlock
                }))}
            >
                <label style={S.checkbox}>
                    <input
                        type="checkbox"
                        checked={s.checkDeadlock}
                        onChange={(e) => update((prev) => ({
                            ...prev, checkDeadlock: e.target.checked
                        }))}
                    />
                    Check deadlock
                    <InfoTip text={TIPS.deadlock} />
                </label>
            </DirtyField>

            <DirtyField
                dirty={!deepEqual(s.invariants, saved.invariants)}
                onUndo={() => revert((sv) => ({
                    invariants: sv.invariants
                }))}
            >
                <TextListField
                    label="Invariants"
                    info="State predicates checked in every reachable state."
                    values={s.invariants}
                    suggestions={discovered.invariantCandidates}
                    onChange={(v) => update((prev) => ({
                        ...prev, invariants: v
                    }))}
                />
            </DirtyField>

            {s.behavior.kind === 'temporal' && (
                <DirtyField
                    dirty={!deepEqual(s.properties, saved.properties)}
                    onUndo={() => revert((sv) => ({
                        properties: sv.properties
                    }))}
                >
                    <TextListField
                        label="Properties"
                        info="Temporal formulas verified over the full behavior graph."
                        values={s.properties}
                        suggestions={discovered.propertyCandidates}
                        onChange={(v) => update((prev) => ({
                            ...prev, properties: v
                        }))}
                    />
                </DirtyField>
            )}
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                WHAT IS THE MODEL (CONSTANTS)
                <InfoTip text={TIPS.constants} />
            </h2>
            {s.constants.length === 0 && (
                <div style={S.smallText}>
                    No CONSTANT declarations were discovered.
                </div>
            )}
            <DirtyField
                dirty={!deepEqual(s.constants, saved.constants)}
                onUndo={() => revert((sv) => ({
                    constants: sv.constants
                }))}
            >
                {s.constants.map((c, i) => (
                    <div key={c.name} style={S.constantRow}>
                        <div style={S.constantName}>{c.name}</div>
                        <select
                            style={S.compactInput}
                            value={c.kind}
                            onChange={(e) => {
                                const k = e.target.value as
                                    ConstantAssignmentKind;
                                update((prev) => {
                                    const cs = [...prev.constants];
                                    cs[i] = { ...cs[i], kind: k };
                                    return { ...prev, constants: cs };
                                });
                            }}
                        >
                            <option value="ordinary">
                                Ordinary assignment
                            </option>
                            <option value="modelValue">
                                Model value
                            </option>
                            <option value="setModelValues">
                                Set of model values
                            </option>
                        </select>
                        <input
                            style={S.input}
                            value={c.value}
                            placeholder={placeholderForKind(c.kind)}
                            onChange={(e) => update((prev) => {
                                const cs = [...prev.constants];
                                cs[i] = {
                                    ...cs[i], value: e.target.value
                                };
                                return { ...prev, constants: cs };
                            })}
                        />
                    </div>
                ))}
            </DirtyField>
        </section>
    </>);
}

function SpecOptionsTab(props: {
    state: ModelEditorState;
    saved: ModelEditorState;
    update: (fn: (s: ModelEditorState) => ModelEditorState) => void;
    revert: (fn: (saved: ModelEditorState) => Partial<ModelEditorState>) => void;
}) {
    const { state: s, saved, update, revert } = props;

    return (<>
        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                STATE CONSTRAINT
                <InfoTip text={TIPS.stateConstraint} />
            </h2>
            <DirtyField
                dirty={s.stateConstraint !== saved.stateConstraint}
                onUndo={() => revert((sv) => ({
                    stateConstraint: sv.stateConstraint
                }))}
            >
                <TextField
                    label="Constraint expression"
                    value={s.stateConstraint}
                    placeholder="e.g. Len(queue) < 5"
                    onChange={(v) => update((prev) => ({
                        ...prev, stateConstraint: v
                    }))}
                />
            </DirtyField>
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                ACTION CONSTRAINT
                <InfoTip text={TIPS.actionConstraint} />
            </h2>
            <DirtyField
                dirty={s.actionConstraint !== saved.actionConstraint}
                onUndo={() => revert((sv) => ({
                    actionConstraint: sv.actionConstraint
                }))}
            >
                <TextField
                    label="Action constraint expression"
                    value={s.actionConstraint}
                    placeholder="e.g. TotalMessages' < 100"
                    onChange={(v) => update((prev) => ({
                        ...prev, actionConstraint: v
                    }))}
                />
            </DirtyField>
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                DEFINITION OVERRIDES
                <InfoTip text={TIPS.defOverrides} />
            </h2>
            <DirtyField
                dirty={!deepEqual(
                    s.definitionOverrides, saved.definitionOverrides
                )}
                onUndo={() => revert((sv) => ({
                    definitionOverrides: sv.definitionOverrides
                }))}
            >
                {s.definitionOverrides.map((o, i) => (
                    <div key={i} style={S.overrideRow}>
                        <input
                            style={S.input}
                            value={o.name}
                            placeholder="Original operator"
                            onChange={(e) => update((prev) => {
                                const ovs = [...prev.definitionOverrides];
                                ovs[i] = { ...ovs[i], name: e.target.value };
                                return {
                                    ...prev, definitionOverrides: ovs
                                };
                            })}
                        />
                        <span style={S.arrow}>→</span>
                        <input
                            style={S.input}
                            value={o.expression}
                            placeholder="Override expression"
                            onChange={(e) => update((prev) => {
                                const ovs = [...prev.definitionOverrides];
                                ovs[i] = {
                                    ...ovs[i], expression: e.target.value
                                };
                                return {
                                    ...prev, definitionOverrides: ovs
                                };
                            })}
                        />
                        <button
                            style={S.removeButton}
                            onClick={() => update((prev) => ({
                                ...prev,
                                definitionOverrides:
                                    prev.definitionOverrides.filter(
                                        (_, j) => j !== i
                                    )
                            }))}
                            title="Remove override"
                        >✕</button>
                    </div>
                ))}
                <button
                    style={S.addButton}
                    onClick={() => update((prev) => ({
                        ...prev,
                        definitionOverrides: [
                            ...prev.definitionOverrides,
                            { name: '', expression: '' }
                        ]
                    }))}
                >+ Add override</button>
            </DirtyField>
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                ADDITIONAL DEFINITIONS
                <InfoTip text={TIPS.additionalDefs} />
            </h2>
            <DirtyField
                dirty={s.additionalDefinitions
                    !== saved.additionalDefinitions}
                onUndo={() => revert((sv) => ({
                    additionalDefinitions: sv.additionalDefinitions
                }))}
            >
                <TextArea
                    label="TLA+ definitions"
                    value={s.additionalDefinitions}
                    placeholder={'e.g.\nMaxVal == 10\nASSUME MaxVal > 0'}
                    onChange={(v) => update((prev) => ({
                        ...prev, additionalDefinitions: v
                    }))}
                />
            </DirtyField>
        </section>
    </>);
}

function TlcOptionsTab() {
    return (
        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                TLC OPTIONS
                <InfoTip text={TIPS.tlcOptions} />
            </h2>
            <div style={S.smallText}>
                TLC options (workers, simulation mode, profiling, etc.)
                are coming in a future update. For now, configure them
                via the <code>tlaplus.tlc.modelChecker.options</code>
                {' '}setting or the options prompt when running TLC.
            </div>
        </section>
    );
}

// ── App Main ─────────────────────────────────────────────

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

    React.useEffect(() => {
        vsCodeApi.postMessage({ command: 'ready' });
        const listener = (event: MessageEvent<{
            type?: string;
            data?: ModelEditorPanelData;
            discovered?: DiscoveredSpecInfo;
            message?: string;
        }>) => {
            if (event.data?.type === 'init' && event.data.data) {
                setData(event.data.data);
                setSavedState(
                    JSON.parse(JSON.stringify(event.data.data.state))
                );
                vsCodeApi.setState(event.data.data);
            } else if (event.data?.type === 'saved') {
                setError('');
                setData((prev) => {
                    if (prev) {
                        const snap = JSON.parse(
                            JSON.stringify(prev.state)
                        );
                        setSavedState(snap);
                        vsCodeApi.setState(prev);
                    }
                    return prev;
                });
            } else if (event.data?.type === 'error') {
                setError(event.data.message ?? 'Error.');
            } else if (event.data?.type === 'requestReady') {
                vsCodeApi.postMessage({ command: 'ready' });
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

    const { state, discovered, unsupportedDirectives } = data;
    const dirty = isAnyDirty(state, savedState);

    const saveModel = () => {
        vsCodeApi.postMessage({ command: 'saveModel', state });
    };

    const saveAndRun = () => {
        vsCodeApi.postMessage({ command: 'saveAndRun', state });
    };

    const openFile = (pathOrKind: string) => {
        vsCodeApi.postMessage({
            command: 'openFile', path: pathOrKind
        });
    };

    return (
        <div style={S.page}>
            <h1 style={S.heading}>TLA+ Model Editor</h1>

            {unsupportedDirectives.length > 0 && (
                <div style={S.warning}>
                    ⚠ The existing config uses directives not yet
                    supported by the editor:{' '}
                    <strong>
                        {unsupportedDirectives.join(', ')}
                    </strong>.
                    Saving will not preserve them.
                </div>
            )}

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
                        <div style={S.smallText}>
                            <a
                                style={S.fileLink}
                                href="#"
                                onClick={(e) => {
                                    e.preventDefault();
                                    openFile('tla');
                                }}
                            >{state.modelName}.tla</a>
                            {' / '}
                            <a
                                style={S.fileLink}
                                href="#"
                                onClick={(e) => {
                                    e.preventDefault();
                                    openFile('cfg');
                                }}
                            >{state.modelName}.cfg</a>
                        </div>
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
            {activeTab === 'tlcOptions' && <TlcOptionsTab />}
        </div>
    );
}

// ── Helpers ───────────────────────────────────────────────────────

function placeholderForKind(kind: ConstantAssignmentKind): string {
    if (kind === 'modelValue') { return 'e.g. NodeA'; }
    if (kind === 'setModelValues') { return 'e.g. a, b, c'; }
    return 'e.g. 1..3 or {"a", "b"}';
}

// ── Styles ────────────────────────────────────────────────────────

const S: Record<string, React.CSSProperties> = {
    page: {
        fontFamily: 'var(--vscode-font-family)',
        color: 'var(--vscode-foreground)',
        padding: '16px',
        maxWidth: '980px',
        margin: '0 auto'
    },
    heading: { fontSize: '1.5rem', marginBottom: '0.5rem' },
    warning: {
        padding: '10px 12px',
        marginBottom: '16px',
        borderRadius: '6px',
        border: '1px solid var(--vscode-inputValidation-warningBorder)',
        background: 'var(--vscode-inputValidation-warningBackground)',
        color: 'var(--vscode-foreground)',
        fontSize: '0.9rem'
    },
    section: {
        border: '1px solid var(--vscode-panel-border)',
        borderRadius: '6px',
        padding: '12px',
        marginBottom: '16px'
    },
    label: { display: 'block', marginBottom: '8px' },
    input: {
        width: '100%',
        marginTop: '4px',
        padding: '6px 8px',
        color: 'var(--vscode-input-foreground)',
        background: 'var(--vscode-input-background)',
        border: '1px solid var(--vscode-input-border)',
        borderRadius: '4px',
        boxSizing: 'border-box'
    },
    compactInput: {
        minWidth: '180px',
        padding: '6px 8px',
        color: 'var(--vscode-input-foreground)',
        background: 'var(--vscode-dropdown-background)',
        border: '1px solid var(--vscode-dropdown-border)',
        borderRadius: '4px'
    },
    fileLink: {
        color: 'var(--vscode-textLink-foreground)',
        textDecoration: 'none',
        cursor: 'pointer'
    },
    button: {
        padding: '6px 12px',
        color: 'var(--vscode-button-foreground)',
        background: 'var(--vscode-button-background)',
        border: 'none',
        borderRadius: '4px',
        cursor: 'pointer'
    },
    buttonPrimary: {
        padding: '6px 12px',
        color: 'var(--vscode-button-foreground)',
        background: 'var(--vscode-button-background)',
        border: 'none',
        borderRadius: '4px',
        cursor: 'pointer',
        fontWeight: 600
    },
    buttonDisabled: {
        opacity: 0.5,
        cursor: 'default'
    },
    buttonGroup: { display: 'flex', gap: '8px' },
    initNextSummary: {
        display: 'flex',
        alignItems: 'center',
        gap: '10px',
        marginTop: '4px'
    },
    linkButton: {
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-textLink-foreground)',
        cursor: 'pointer',
        fontSize: '0.85rem',
        padding: '0',
        textDecoration: 'underline'
    },
    headerRow: {
        display: 'flex',
        justifyContent: 'space-between',
        gap: '12px',
        alignItems: 'center'
    },
    smallText: {
        fontSize: '0.85rem',
        color: 'var(--vscode-descriptionForeground)'
    },
    errorText: {
        marginTop: '8px',
        fontSize: '0.9rem',
        color: 'var(--vscode-errorForeground)'
    },
    checkbox: {
        display: 'flex',
        gap: '8px',
        alignItems: 'center',
        marginBottom: '8px'
    },
    grid: {
        display: 'grid',
        gridTemplateColumns: 'repeat(auto-fit, minmax(240px, 1fr))',
        gap: '12px'
    },
    listField: { marginTop: '8px' },
    suggestionRow: {
        display: 'flex',
        flexWrap: 'wrap',
        gap: '6px',
        marginTop: '6px'
    },
    chip: {
        padding: '4px 8px',
        borderRadius: '12px',
        border: '1px solid var(--vscode-panel-border)',
        background: 'var(--vscode-editor-background)',
        color: 'var(--vscode-foreground)',
        cursor: 'pointer',
        fontSize: '0.85rem'
    },
    constantRow: {
        display: 'grid',
        gridTemplateColumns: '140px 200px 1fr',
        gap: '10px',
        alignItems: 'center',
        marginBottom: '8px'
    },
    constantName: { fontWeight: 600 },

    // Tab bar
    tabBar: {
        display: 'flex',
        gap: '0',
        marginBottom: '16px'
    },
    tabWrap: {
        flex: 1,
        display: 'flex',
        flexDirection: 'column' as const
    },
    tab: {
        flex: 1,
        padding: '8px 16px',
        background: 'transparent',
        color: 'var(--vscode-foreground)',
        border: 'none',
        cursor: 'pointer',
        fontSize: '0.9rem',
        opacity: 0.7,
        textAlign: 'center',
        outline: 'none'
    },
    tabActiveText: {
        opacity: 1,
        fontWeight: 600
    },
    tabIndicator: {
        height: '2px',
        background: 'var(--vscode-focusBorder)'
    },
    tabIndicatorHidden: {
        height: '2px',
        background: 'transparent'
    },

    // InfoTip (inline tooltip icon)
    infoTipWrap: {
        position: 'relative',
        display: 'inline-block',
        marginLeft: '6px',
        verticalAlign: 'middle',
        cursor: 'help'
    },
    infoTipIcon: {
        fontSize: '0.85rem',
        color: 'var(--vscode-descriptionForeground)',
        opacity: 0.7
    },
    infoTipPopover: {
        position: 'absolute',
        top: 'calc(100% + 6px)',
        left: '0',
        width: '280px',
        padding: '8px 12px',
        borderRadius: '4px',
        background: 'var(--vscode-editorHoverWidget-background)',
        border: '1px solid var(--vscode-editorHoverWidget-border)',
        color: 'var(--vscode-editorHoverWidget-foreground)',
        fontSize: '0.82rem',
        lineHeight: '1.45',
        zIndex: 100,
        pointerEvents: 'none',
        boxShadow: '0 2px 8px rgba(0,0,0,0.3)'
    },

    // Section heading (uppercase label with inline info)
    sectionHeading: {
        fontSize: '0.8rem',
        fontWeight: 600,
        letterSpacing: '0.5px',
        textTransform: 'uppercase' as const,
        color: 'var(--vscode-descriptionForeground)',
        marginBottom: '12px',
        display: 'flex',
        alignItems: 'center'
    },

    // Field label (inline with info tip)
    fieldLabel: {
        display: 'flex',
        alignItems: 'center',
        gap: '4px',
        marginBottom: '8px',
        flexWrap: 'wrap' as const
    },

    // Dirty field
    dirtyField: {
        position: 'relative',
        paddingLeft: '8px',
        marginBottom: '4px'
    },
    dirtyFieldHighlight: {
        borderLeft: '3px solid var(--vscode-editorWarning-foreground)',
        paddingLeft: '5px'
    },
    undoButton: {
        position: 'absolute',
        top: '0',
        right: '0',
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-descriptionForeground)',
        cursor: 'pointer',
        fontSize: '1rem',
        padding: '2px 6px'
    },

    // Spec options
    overrideRow: {
        display: 'grid',
        gridTemplateColumns: '1fr auto 1fr auto',
        gap: '8px',
        alignItems: 'center',
        marginBottom: '8px'
    },
    arrow: {
        color: 'var(--vscode-descriptionForeground)',
        fontSize: '1.1rem'
    },
    removeButton: {
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-errorForeground)',
        cursor: 'pointer',
        fontSize: '1rem',
        padding: '2px 6px'
    },
    addButton: {
        padding: '4px 10px',
        background: 'transparent',
        border: '1px dashed var(--vscode-panel-border)',
        borderRadius: '4px',
        color: 'var(--vscode-foreground)',
        cursor: 'pointer',
        fontSize: '0.85rem',
        marginTop: '4px'
    },

    // Custom suggestion dropdown (replaces native datalist)
    suggestBox: {
        position: 'absolute',
        top: '100%',
        left: '0',
        right: '0',
        maxHeight: '160px',
        overflowY: 'auto',
        background: 'var(--vscode-editorSuggestWidget-background)',
        border: '1px solid var(--vscode-editorSuggestWidget-border)',
        borderRadius: '4px',
        zIndex: 200,
        boxShadow: '0 2px 8px rgba(0,0,0,0.3)'
    },
    suggestItem: {
        padding: '4px 10px',
        cursor: 'pointer',
        fontSize: '0.9rem',
        color: 'var(--vscode-editorSuggestWidget-foreground)'
    }
};

// ── Mount ─────────────────────────────────────────────────────────

createRoot(
    document.getElementById('root') as HTMLElement
).render(<App />);
