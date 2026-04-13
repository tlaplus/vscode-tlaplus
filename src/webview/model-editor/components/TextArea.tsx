import * as React from 'react';
import { S } from '../styles';

export function TextArea(props: {
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
