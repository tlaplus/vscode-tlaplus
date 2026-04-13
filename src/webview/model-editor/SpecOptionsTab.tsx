import * as React from 'react';
import { S } from './styles';
import { TIPS } from './tips';
import { deepEqual } from './dirty';
import { InfoTip, DirtyField } from './components';
import type { ModelEditorState } from '../../model/modelEditorFiles';

export function SpecOptionsTab(props: {
    state: ModelEditorState;
    saved: ModelEditorState;
    update: (fn: (s: ModelEditorState) => ModelEditorState) => void;
    revert: (fn: (saved: ModelEditorState) => Partial<ModelEditorState>) => void;
}) {
    const { state: s, saved, update, revert } = props;

    return (<>
        <section style={S.section}>
            <h2 style={S.sectionHeading}>CONSTRAINTS</h2>

            <DirtyField
                dirty={s.stateConstraint !== saved.stateConstraint}
                onUndo={() => revert((sv) => ({
                    stateConstraint: sv.stateConstraint
                }))}
            >
                <label style={S.fieldLabel}>
                    State constraint:
                    <InfoTip text={TIPS.stateConstraint} />
                </label>
                <input
                    style={S.input}
                    value={s.stateConstraint}
                    placeholder="e.g. Len(queue) < 5"
                    onChange={(e) => update((prev) => ({
                        ...prev, stateConstraint: e.target.value
                    }))}
                />
            </DirtyField>

            <DirtyField
                dirty={s.actionConstraint !== saved.actionConstraint}
                onUndo={() => revert((sv) => ({
                    actionConstraint: sv.actionConstraint
                }))}
            >
                <label style={S.fieldLabel}>
                    Action constraint:
                    <InfoTip text={TIPS.actionConstraint} />
                </label>
                <input
                    style={S.input}
                    value={s.actionConstraint}
                    placeholder="e.g. TotalMessages' < 100"
                    onChange={(e) => update((prev) => ({
                        ...prev, actionConstraint: e.target.value
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
                                const ovs = [
                                    ...prev.definitionOverrides
                                ];
                                ovs[i] = {
                                    ...ovs[i], name: e.target.value
                                };
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
                                const ovs = [
                                    ...prev.definitionOverrides
                                ];
                                ovs[i] = {
                                    ...ovs[i],
                                    expression: e.target.value
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
            <h2 style={S.sectionHeading}>ADVANCED</h2>

            <DirtyField
                dirty={s.additionalDefinitions
                    !== saved.additionalDefinitions}
                onUndo={() => revert((sv) => ({
                    additionalDefinitions: sv.additionalDefinitions
                }))}
            >
                <label style={S.fieldLabel}>
                    Additional definitions:
                    <InfoTip text={TIPS.additionalDefs} />
                </label>
                <textarea
                    style={{
                        ...S.input,
                        minHeight: '80px',
                        resize: 'vertical'
                    } as React.CSSProperties}
                    value={s.additionalDefinitions}
                    placeholder={'e.g. MaxVal == 10'}
                    onChange={(e) => update((prev) => ({
                        ...prev,
                        additionalDefinitions: e.target.value
                    }))}
                />
            </DirtyField>

            <DirtyField
                dirty={s.viewExpression !== saved.viewExpression}
                onUndo={() => revert((sv) => ({
                    viewExpression: sv.viewExpression
                }))}
            >
                <label style={S.fieldLabel}>
                    View expression:
                    <InfoTip text={TIPS.viewExpr} />
                </label>
                <input
                    style={S.input}
                    value={s.viewExpression}
                    placeholder="e.g. <<pc, stack>>"
                    onChange={(e) => update((prev) => ({
                        ...prev, viewExpression: e.target.value
                    }))}
                />
            </DirtyField>

            <DirtyField
                dirty={s.alias !== saved.alias}
                onUndo={() => revert((sv) => ({
                    alias: sv.alias
                }))}
            >
                <label style={S.fieldLabel}>
                    Alias:
                    <InfoTip text={TIPS.alias} />
                </label>
                <input
                    style={S.input}
                    value={s.alias}
                    placeholder="Operator name"
                    onChange={(e) => update((prev) => ({
                        ...prev, alias: e.target.value
                    }))}
                />
            </DirtyField>

            <DirtyField
                dirty={s.postCondition !== saved.postCondition}
                onUndo={() => revert((sv) => ({
                    postCondition: sv.postCondition
                }))}
            >
                <label style={S.fieldLabel}>
                    Post-condition:
                    <InfoTip text={TIPS.postCondition} />
                </label>
                <input
                    style={S.input}
                    value={s.postCondition}
                    placeholder="Operator name"
                    onChange={(e) => update((prev) => ({
                        ...prev, postCondition: e.target.value
                    }))}
                />
            </DirtyField>
        </section>
    </>);
}
