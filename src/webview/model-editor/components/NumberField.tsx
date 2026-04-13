import * as React from 'react';
import { S } from '../styles';
import { InfoTip } from './InfoTip';

export function NumberField(props: {
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
