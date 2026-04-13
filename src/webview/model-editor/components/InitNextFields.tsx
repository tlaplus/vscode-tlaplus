import * as React from 'react';
import { S } from '../styles';
import type { DiscoveredSpecInfo } from '../../../model/modelEditorFiles';
import { TextField } from './TextField';

export function InitNextFields(props: {
    init: string;
    next: string;
    discovered: DiscoveredSpecInfo;
    onChange: (init: string, next: string) => void;
}) {
    const [expanded, setExpanded] = React.useState(false);
    const hasDefaults = props.init && props.next;

    if (!expanded && hasDefaults) {
        return (
            <div style={S.initNextSummary}>
                <span style={S.smallText}>
                    Init = <strong>{props.init}</strong>,
                    Next = <strong>{props.next}</strong>
                </span>
                <button
                    style={S.linkButton}
                    onClick={() => setExpanded(true)}
                >change</button>
            </div>
        );
    }

    return (
        <div style={S.grid}>
            <TextField
                label="Init"
                value={props.init}
                suggestions={props.discovered.initCandidates}
                onChange={(v) => props.onChange(v, props.next)}
            />
            <TextField
                label="Next"
                value={props.next}
                suggestions={props.discovered.nextCandidates}
                onChange={(v) => props.onChange(props.init, v)}
            />
        </div>
    );
}
