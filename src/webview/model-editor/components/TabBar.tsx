import * as React from 'react';
import { S } from '../styles';
import { isTabDirty } from '../dirty';
import type { TabId } from '../dirty';
import type { ModelEditorState, TlcOptionsState } from '../../../model/modelEditorFiles';

export function TabBar(props: {
    active: TabId;
    onChange: (tab: TabId) => void;
    current: ModelEditorState;
    saved: ModelEditorState;
    currentTlc: TlcOptionsState;
    savedTlc: TlcOptionsState;
}) {
    const tabs: { id: TabId; label: string }[] = [
        { id: 'overview', label: 'Model Overview' },
        { id: 'specOptions', label: 'Spec Options' },
        { id: 'tlcOptions', label: 'TLC Options' },
    ];
    return (
        <div style={S.tabBar}>
            {tabs.map((tab) => {
                const dirty = isTabDirty(
                    tab.id, props.current, props.saved,
                    props.currentTlc, props.savedTlc
                );
                const active = props.active === tab.id;
                return (
                    <div key={tab.id} style={S.tabWrap}>
                        <button
                            style={{
                                ...S.tab,
                                ...(active ? S.tabActiveText : {})
                            }}
                            onClick={() => props.onChange(tab.id)}
                        >
                            {tab.label}{dirty ? ' *' : ''}
                        </button>
                        <div style={active
                            ? S.tabIndicator
                            : S.tabIndicatorHidden}
                        />
                    </div>
                );
            })}
        </div>
    );
}
