import { Value, ValueKey, SetValue, SequenceValue, StructureValue } from '../../model/check';

export function v(key: ValueKey, value: string): Value {
    return new Value(String(key), value);
}

export function set(key: ValueKey, ...values: Value[]): SetValue {
    return new SetValue(key, values);
}

export function seq(key: ValueKey, ...values: Value[]): SequenceValue {
    return new SequenceValue(key, values);
}

export function struct(key: ValueKey, ...values: Value[]): StructureValue {
    return new StructureValue(key, values);
}
