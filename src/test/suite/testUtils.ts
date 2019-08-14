import { Value, ValueKey, SetValue, SequenceValue, StructureValue, SimpleFunction } from '../../model/check';

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

export function func(key: ValueKey, from: Value, to: Value): SimpleFunction {
    return new SimpleFunction(key, from, to);
}
