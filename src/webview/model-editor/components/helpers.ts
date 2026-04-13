import type { ConstantAssignmentKind } from '../../../model/modelEditorFiles';

export function placeholderForKind(kind: ConstantAssignmentKind): string {
    if (kind === 'modelValue') { return 'e.g. NodeA'; }
    if (kind === 'setModelValues') { return 'e.g. a, b, c'; }
    return 'e.g. 1..3 or {"a", "b"}';
}
