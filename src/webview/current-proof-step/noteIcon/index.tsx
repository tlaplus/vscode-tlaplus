import * as React from 'react';
import './index.css';

interface NoteIconI { level: string }
export const NoteIcon = React.memo(({ level }: NoteIconI) => {
    return (
        <span
            className={`codicon codicon-info note-icon note-icon-${level}`}
            title={level}
        ></span>
    );
});
