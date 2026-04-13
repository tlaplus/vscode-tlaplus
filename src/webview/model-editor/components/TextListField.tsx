import * as React from 'react';
import { S } from '../styles';
import { InfoTip } from './InfoTip';

export function TextListField(props: {
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
