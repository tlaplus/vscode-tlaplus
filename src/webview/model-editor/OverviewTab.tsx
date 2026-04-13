import * as React from 'react';
import { S } from './styles';
import { TIPS } from './tips';
import { deepEqual } from './dirty';
import {
    InfoTip,
    DirtyField,
    TextField,
    TextListField,
    InitNextFields,
    placeholderForKind
} from './components';
import type {
    ConstantAssignmentKind,
    DiscoveredSpecInfo,
    ModelEditorState
} from '../../model/modelEditorFiles';


export function OverviewTab(props: {
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
                        {c.kind === 'setModelValues' && (
                            <label style={{
                                display: 'flex',
                                alignItems: 'center',
                                gap: '4px',
                                whiteSpace: 'nowrap' as const
                            }}>
                                <input
                                    type="checkbox"
                                    checked={(s.symmetryConstants ?? [])
                                        .includes(c.name)}
                                    onChange={(e) => {
                                        const on = e.target.checked;
                                        update((prev) => {
                                            const syms = [
                                                ...(prev.symmetryConstants
                                                    ?? [])
                                            ];
                                            if (on
                                                && !syms.includes(c.name)
                                            ) {
                                                syms.push(c.name);
                                            } else if (!on) {
                                                const idx = syms.indexOf(
                                                    c.name
                                                );
                                                if (idx >= 0) {
                                                    syms.splice(idx, 1);
                                                }
                                            }
                                            return {
                                                ...prev,
                                                symmetryConstants: syms
                                            };
                                        });
                                    }}
                                />
                                Symmetry
                                <InfoTip text={TIPS.symmetry} />
                            </label>
                        )}
                    </div>
                ))}
            </DirtyField>
        </section>
    </>);
}
