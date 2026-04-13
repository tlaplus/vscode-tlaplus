import * as React from 'react';
import { S } from '../styles';

export function DirtyField(props: {
    dirty: boolean;
    onUndo: () => void;
    children: React.ReactNode;
}) {
    return (
        <div style={{
            ...S.dirtyField,
            ...(props.dirty ? S.dirtyFieldHighlight : {})
        }}>
            {props.children}
            {props.dirty && (
                <button
                    style={S.undoButton}
                    onClick={props.onUndo}
                    title="Revert to saved value"
                >↩</button>
            )}
        </div>
    );
}
