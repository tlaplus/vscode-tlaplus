import * as React from 'react';
import { S } from '../styles';

export function ModelNameEditor(props: {
    modelName: string;
    onChange: (name: string) => void;
    onOpenFile: (kind: string) => void;
}) {
    const [editing, setEditing] = React.useState(false);
    const [draft, setDraft] = React.useState('');

    const startEdit = () => {
        // Strip the MC prefix for editing
        const suffix = props.modelName.startsWith('MC')
            ? props.modelName.substring(2)
            : props.modelName;
        setDraft(suffix);
        setEditing(true);
    };

    const confirm = () => {
        const trimmed = draft.trim();
        if (trimmed) {
            props.onChange(`MC${trimmed}`);
        }
        setEditing(false);
    };

    const cancel = () => setEditing(false);

    if (editing) {
        return (
            <div style={S.modelNameEdit}>
                <span style={S.smallText}>MC</span>
                <input
                    style={{ ...S.input, width: '160px' }}
                    value={draft}
                    autoFocus
                    onChange={(e) => setDraft(e.target.value)}
                    onKeyDown={(e) => {
                        if (e.key === 'Enter') { confirm(); }
                        if (e.key === 'Escape') { cancel(); }
                    }}
                />
                <span style={S.smallText}>.tla / .cfg</span>
                <button style={S.chipButton} onClick={confirm}>
                    ✓
                </button>
                <button style={S.chipButton} onClick={cancel}>
                    ✕
                </button>
            </div>
        );
    }

    return (
        <div style={S.modelNameRow}>
            <a style={S.fileLink} href="#" onClick={(e) => {
                e.preventDefault(); props.onOpenFile('tla');
            }}>{props.modelName}.tla</a>
            {' / '}
            <a style={S.fileLink} href="#" onClick={(e) => {
                e.preventDefault(); props.onOpenFile('cfg');
            }}>{props.modelName}.cfg</a>
            <button
                style={S.chipButton}
                onClick={startEdit}
                title="Rename model files"
            >✎</button>
        </div>
    );
}
