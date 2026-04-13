import * as React from 'react';
import { createRoot } from 'react-dom/client';
import { vsCodeApi } from './common/vscode_api';
import type {
    ConstantAssignmentKind,
    DiscoveredSpecInfo,
    ModelEditorState,
    TlcOptionsState
} from '../model/modelEditorFiles';

// ── Types ─────────────────────────────────────────────────────────

type TabId = 'overview' | 'specOptions' | 'tlcOptions';

interface ModelEditorPanelData {
    state: ModelEditorState;
    discovered: DiscoveredSpecInfo;
    unsupportedDirectives: string[];
    tlcOptions?: TlcOptionsState;
}

// ── Dirty-tracking helpers ──────────────────────────────────────

function deepEqual(a: unknown, b: unknown): boolean {
    return JSON.stringify(a) === JSON.stringify(b);
}

function isTabDirty(
    tab: TabId,
    current: ModelEditorState,
    saved: ModelEditorState,
    currentTlc?: TlcOptionsState,
    savedTlc?: TlcOptionsState
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
    if (tab === 'tlcOptions') {
        return !deepEqual(currentTlc, savedTlc);
    }
    return false;
}

function isAnyDirty(
    current: ModelEditorState,
    saved: ModelEditorState,
    currentTlc?: TlcOptionsState,
    savedTlc?: TlcOptionsState
): boolean {
    return !deepEqual(current, saved)
        || !deepEqual(currentTlc, savedTlc);
}

// ── Tooltip texts ─────────────────────────────

/* eslint-disable max-len */
const TIPS = {
    behaviorSpec: 'Choose how TLC explores your system. This tells TLC where to start and how states evolve over time.',
    mode: 'Init/Next is the most common — provide an initial-state predicate and a next-state relation. Temporal formula uses a single operator like Spec that combines fairness conditions. No behavior spec lets you evaluate constant expressions without state exploration.',
    deadlock: 'When enabled, TLC verifies every reachable state has at least one successor. Disable this if your spec intentionally has terminal states (e.g. a protocol that completes).',
    invariants: 'State predicates that must hold in every reachable state. Use these to catch safety violations — for example, TypeOK to verify variables stay within expected types.',
    properties: 'Temporal formulas checked over the full behavior graph. Use these for liveness properties — for example, verifying that every request eventually gets a response.',
    constants: 'TLC needs concrete values for each CONSTANT in your spec. Use ordinary assignment for expressions like 1..3, model value for unique identifiers, or set of model values for finite enumerated sets.',
    stateConstraint: 'Limits which states TLC explores by requiring this expression to be TRUE. Use this to make large or infinite models tractable — for example, Len(queue) < 5 to cap queue size during exploration.',
    actionConstraint: 'Filters which transitions TLC considers by requiring this expression over current and next-state variables to be TRUE. Useful for focusing model checking on specific scenarios — for example, only exploring paths where message count stays bounded.',
    defOverrides: 'Replaces spec operators with model-specific definitions during checking. Essential for making infinite sets finite — for example, overriding Nat with 0..10 so TLC can enumerate values.',
    additionalDefs: 'Extra TLA+ definitions added to the MC module. Use this for helper operators needed by constraints or overrides, or for ASSUME statements that validate model parameters.',
    tlcOptions: 'Controls how TLC runs: checking strategy, parallelism, and diagnostics. These are command-line arguments, not part of the .cfg file.',
    checkingMode: 'BFS (breadth-first) explores all states and finds the shortest counterexamples. DFID uses less memory for very large state spaces. Simulation generates random behaviors and is useful for quick smoke tests or exploring specs that are too large to check exhaustively.',
    workers: 'Number of parallel threads. Set to 0 to automatically use all available CPU cores (recommended). More workers check faster but use more memory.',
    dfidDepth: 'Maximum search depth for depth-first iterative deepening. Deeper values explore more of the state space but take longer.',
    simTraces: 'How many random traces to generate. Set to 0 for unlimited (runs until you stop it). Higher values give more confidence but take longer.',
    simSeed: 'A fixed seed makes simulation reproducible — the same seed always generates the same traces. Useful for debugging a specific counterexample.',
    fpBits: 'Controls the fingerprint function used to identify states. Higher values reduce the probability of hash collisions (false matches) but use more memory. The default of 1 is fine for most models.',
    profiling: 'Shows how often each expression is evaluated during model checking. Useful for finding performance bottlenecks in your spec — results appear in the TLC coverage panel.',
    viewExpr: 'A TLA+ expression evaluated in each state and included in error traces. Use this to see computed values (like queue lengths or message counts) alongside raw state variables in counterexamples.',
    postCondition: 'An operator evaluated after model checking finishes. It receives the set of all reachable states, useful for computing statistics or asserting global properties of the state graph.',
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
    currentTlc: TlcOptionsState;
    savedTlc: TlcOptionsState;
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
                    tab.id, props.current, props.saved,
                    props.currentTlc, props.savedTlc
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

function ModelNameEditor(props: {
    modelName: string;
    onChange: (name: string) => void;
    onOpenFile: (kind: string) => void;
}) {
    const [editing, setEditing] = React.useState(false);
    const [draft, setDraft] = React.useState('');

    const startEdit = () => {
        // Strip the MC prefix for editing
        const suffix = props.modelName.startsWith('MC')
            ? props.modelName.substring(2)
            : props.modelName;
        setDraft(suffix);
        setEditing(true);
    };

    const confirm = () => {
        const trimmed = draft.trim();
        if (trimmed) {
            props.onChange(`MC${trimmed}`);
        }
        setEditing(false);
    };

    const cancel = () => setEditing(false);

    if (editing) {
        return (
            <div style={S.modelNameEdit}>
                <span style={S.smallText}>MC</span>
                <input
                    style={{ ...S.input, width: '160px' }}
                    value={draft}
                    autoFocus
                    onChange={(e) => setDraft(e.target.value)}
                    onKeyDown={(e) => {
                        if (e.key === 'Enter') { confirm(); }
                        if (e.key === 'Escape') { cancel(); }
                    }}
                />
                <span style={S.smallText}>.tla / .cfg</span>
                <button style={S.chipButton} onClick={confirm}>
                    ✓
                </button>
                <button style={S.chipButton} onClick={cancel}>
                    ✕
                </button>
            </div>
        );
    }

    return (
        <div style={S.modelNameRow}>
            <a style={S.fileLink} href="#" onClick={(e) => {
                e.preventDefault(); props.onOpenFile('tla');
            }}>{props.modelName}.tla</a>
            {' / '}
            <a style={S.fileLink} href="#" onClick={(e) => {
                e.preventDefault(); props.onOpenFile('cfg');
            }}>{props.modelName}.cfg</a>
            <button
                style={S.chipButton}
                onClick={startEdit}
                title="Rename model files"
            >✎</button>
        </div>
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
                            style={{
                                ...S.input,
                                flex: '1 1 150px',
                                width: 'auto'
                            }}
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
                            style={{
                                ...S.input,
                                flex: '1 1 120px',
                                width: 'auto'
                            }}
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
                            style={{
                                ...S.input,
                                flex: '1 1 120px',
                                width: 'auto'
                            }}
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

function TlcOptionsTab(props: {
    opts: TlcOptionsState;
    onChange: (fn: (o: TlcOptionsState) => TlcOptionsState) => void;
}) {
    const { opts, onChange } = props;
    const set = <K extends keyof TlcOptionsState>(
        key: K, value: TlcOptionsState[K]
    ) => onChange((prev) => ({ ...prev, [key]: value }));

    return (<>
        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                CHECKING MODE
                <InfoTip text={TIPS.checkingMode} />
            </h2>
            <div style={{ marginBottom: '12px' }}>
                {(['bfs', 'dfid', 'simulate'] as const).map((m) => (
                    <label key={m} style={S.radioLabel}>
                        <input
                            type="radio"
                            name="checkingMode"
                            checked={opts.checkingMode === m}
                            onChange={() => set('checkingMode', m)}
                        />
                        {{
                            bfs: 'Model checking (BFS)',
                            dfid: 'Depth-first (DFID)',
                            simulate: 'Simulation'
                        }[m]}
                    </label>
                ))}
            </div>

            {opts.checkingMode === 'dfid' && (
                <NumberField
                    label="Max depth"
                    info={TIPS.dfidDepth}
                    value={opts.dfidDepth}
                    onChange={(v) => set('dfidDepth', v)}
                />
            )}

            {opts.checkingMode === 'simulate' && (<>
                <NumberField
                    label="Number of traces (0 = unlimited)"
                    info={TIPS.simTraces}
                    value={opts.simulateTraces}
                    onChange={(v) => set('simulateTraces', v)}
                />
                <TextField
                    label="Seed"
                    value={opts.simulateSeed}
                    placeholder="Leave empty for random"
                    onChange={(v) => set('simulateSeed', v)}
                />
            </>)}
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>RESOURCES</h2>
            <label style={S.fieldLabel}>
                Workers (threads):
                <InfoTip text={TIPS.workers} />
                <input
                    style={{ ...S.input, width: '120px' }}
                    type="number"
                    value={opts.workers}
                    min={0}
                    onChange={(e) => set('workers',
                        parseInt(e.target.value, 10) || 0
                    )}
                />
                {opts.workers === 0 && (
                    <span style={S.smallText}>
                        (0 = auto, uses all available CPU cores)
                    </span>
                )}
            </label>
            <NumberField
                label="Fingerprint bits"
                info={TIPS.fpBits}
                value={opts.fpBits}
                min={0}
                onChange={(v) => set('fpBits', v)}
            />
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>ADVANCED</h2>
            <label style={S.checkbox}>
                <input
                    type="checkbox"
                    checked={opts.enableProfiling}
                    onChange={(e) => set(
                        'enableProfiling', e.target.checked
                    )}
                />
                Enable profiling
                <InfoTip text={TIPS.profiling} />
            </label>
            <label style={S.fieldLabel}>
                View expression:
                <InfoTip text={TIPS.viewExpr} />
            </label>
            <TextField
                label=""
                value={opts.viewExpression}
                placeholder="e.g. <<pc, stack>>"
                onChange={(v) => set('viewExpression', v)}
            />
            <label style={S.fieldLabel}>
                Post-condition:
                <InfoTip text={TIPS.postCondition} />
            </label>
            <TextField
                label=""
                value={opts.postCondition}
                placeholder="Operator name"
                onChange={(v) => set('postCondition', v)}
            />
        </section>
    </>);
}

function NumberField(props: {
    label: string;
    info?: string;
    value: number;
    min?: number;
    onChange: (v: number) => void;
}) {
    return (
        <label style={S.fieldLabel}>
            {props.label}:
            {props.info && <InfoTip text={props.info} />}
            <input
                style={{ ...S.input, width: '120px' }}
                type="number"
                value={props.value}
                min={props.min}
                onChange={(e) => props.onChange(
                    parseInt(e.target.value, 10) || 0
                )}
            />
        </label>
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
    const defaultTlcOpts: TlcOptionsState = {
        checkingMode: 'bfs', workers: 0, dfidDepth: 100,
        simulateTraces: 0, simulateSeed: '', fpBits: 1,
        enableProfiling: false, viewExpression: '', postCondition: ''
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

    const { state, discovered, unsupportedDirectives } = data;
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
        padding: '12px',
        maxWidth: '980px',
        margin: '0 auto',
        boxSizing: 'border-box' as const
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
    modelNameRow: {
        display: 'flex',
        alignItems: 'center',
        flexWrap: 'wrap' as const,
        gap: '6px',
        fontSize: '0.85rem',
        color: 'var(--vscode-descriptionForeground)'
    },
    modelNameEdit: {
        display: 'flex',
        alignItems: 'center',
        flexWrap: 'wrap' as const,
        gap: '4px',
        marginTop: '2px'
    },
    chipButton: {
        background: 'transparent',
        border: 'none',
        color: 'var(--vscode-descriptionForeground)',
        cursor: 'pointer',
        fontSize: '0.9rem',
        padding: '2px 4px'
    },
    button: {
        padding: '6px 12px',
        color: 'var(--vscode-button-foreground)',
        background: 'var(--vscode-button-background)',
        border: 'none',
        borderRadius: '4px',
        cursor: 'pointer',
        whiteSpace: 'nowrap' as const
    },
    buttonPrimary: {
        padding: '6px 12px',
        color: 'var(--vscode-button-foreground)',
        background: 'var(--vscode-button-background)',
        border: 'none',
        borderRadius: '4px',
        cursor: 'pointer',
        fontWeight: 600,
        whiteSpace: 'nowrap' as const
    },
    buttonDisabled: {
        opacity: 0.5,
        cursor: 'default'
    },
    buttonGroup: {
        display: 'flex',
        gap: '8px',
        flexShrink: 0,
        flexWrap: 'wrap' as const
    },
    radioLabel: {
        display: 'flex',
        alignItems: 'center',
        gap: '8px',
        marginBottom: '6px',
        cursor: 'pointer'
    },
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
        alignItems: 'flex-start',
        flexWrap: 'wrap' as const
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
        display: 'flex',
        flexWrap: 'wrap' as const,
        gap: '8px',
        alignItems: 'center',
        marginBottom: '8px'
    },
    constantName: { fontWeight: 600 },

    // Tab bar
    tabBar: {
        display: 'flex',
        flexWrap: 'wrap' as const,
        gap: '0',
        marginBottom: '16px'
    },
    tabWrap: {
        flex: '1 1 0',
        minWidth: '100px',
        display: 'flex',
        flexDirection: 'column' as const
    },
    tab: {
        padding: '8px 10px',
        background: 'transparent',
        color: 'var(--vscode-foreground)',
        border: 'none',
        cursor: 'pointer',
        fontSize: '0.9rem',
        opacity: 0.7,
        textAlign: 'center',
        outline: 'none',
        whiteSpace: 'nowrap' as const
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
        textTransform: 'none' as const,
        letterSpacing: 'normal',
        fontWeight: 'normal' as const,
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
        display: 'flex',
        flexWrap: 'wrap' as const,
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
