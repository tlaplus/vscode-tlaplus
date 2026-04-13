import type {
    ModelEditorState,
    TlcOptionsState
} from '../../model/modelEditorFiles';


export type TabId = 'overview' | 'specOptions' | 'tlcOptions';


export function deepEqual(a: unknown, b: unknown): boolean {
    return JSON.stringify(a) === JSON.stringify(b);
}

export function isTabDirty(
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
            || !deepEqual(current.properties, saved.properties)
            || !deepEqual(
                current.symmetryConstants, saved.symmetryConstants
            );
    }
    if (tab === 'specOptions') {
        return current.stateConstraint !== saved.stateConstraint
            || current.actionConstraint !== saved.actionConstraint
            || !deepEqual(
                current.definitionOverrides, saved.definitionOverrides
            )
            || current.additionalDefinitions
                !== saved.additionalDefinitions
            || current.viewExpression !== saved.viewExpression
            || current.alias !== saved.alias
            || current.postCondition !== saved.postCondition;
    }
    if (tab === 'tlcOptions') {
        return !deepEqual(currentTlc, savedTlc);
    }
    return false;
}

export function isAnyDirty(
    current: ModelEditorState,
    saved: ModelEditorState,
    currentTlc?: TlcOptionsState,
    savedTlc?: TlcOptionsState
): boolean {
    return !deepEqual(current, saved)
        || !deepEqual(currentTlc, savedTlc);
}
