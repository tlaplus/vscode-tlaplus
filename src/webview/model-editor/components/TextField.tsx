import * as React from 'react';
import { S } from '../styles';

export function TextField(props: {
    label: string;
    value: string;
    suggestions?: string[];
    placeholder?: string;
    onChange: (value: string) => void;
}) {
    const [focused, setFocused] = React.useState(false);
    const wrapRef = React.useRef<HTMLLabelElement>(null);

    const filtered = (props.suggestions ?? []).filter(
        (s) => s.toLowerCase().includes(
            props.value.toLowerCase()
        ) && s !== props.value
    );
    const showSuggestions = focused && filtered.length > 0;

    return (
        <label
            style={{ ...S.label, position: 'relative' }}
            ref={wrapRef}
        >
            {props.label}
            <input
                style={S.input}
                value={props.value}
                placeholder={props.placeholder}
                onChange={(e) => props.onChange(e.target.value)}
                onFocus={() => setFocused(true)}
                onBlur={() => setTimeout(
                    () => setFocused(false), 150
                )}
            />
            {showSuggestions && (
                <div style={S.suggestBox}>
                    {filtered.map((s) => (
                        <div
                            key={s}
                            style={S.suggestItem}
                            onMouseDown={(e) => {
                                e.preventDefault();
                                props.onChange(s);
                                setFocused(false);
                            }}
                        >{s}</div>
                    ))}
                </div>
            )}
        </label>
    );
}
