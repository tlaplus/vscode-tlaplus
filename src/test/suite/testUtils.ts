import { Value, ValueKey, SetValue, SequenceValue, StructureValue } from '../../model/check';

export function v(key: ValueKey, value: string): Value {
    return new Value(String(key), value);
}

export function set(key: ValueKey, ...items: Value[]): SetValue {
    return new SetValue(key, items);
}

export function seq(key: ValueKey, ...items: Value[]): SequenceValue {
    return new SequenceValue(key, items);
}

export function struct(key: ValueKey, ...items: Value[]): StructureValue {
    return new StructureValue(key, items);
}
