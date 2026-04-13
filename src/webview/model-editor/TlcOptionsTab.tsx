import * as React from 'react';
import { S } from './styles';
import { TIPS } from './tips';
import { InfoTip, TextField, NumberField } from './components';
import type { TlcOptionsState } from '../../model/modelEditorFiles';

export function TlcOptionsTab(props: {
    opts: TlcOptionsState;
    onChange: (fn: (o: TlcOptionsState) => TlcOptionsState) => void;
}) {
    const { opts, onChange } = props;
    const set = <K extends keyof TlcOptionsState>(
        key: K, value: TlcOptionsState[K]
    ) => onChange((prev) => ({ ...prev, [key]: value }));

    return (<>
        <section style={S.section}>
            <h2 style={S.sectionHeading}>
                CHECKING MODE
                <InfoTip text={TIPS.checkingMode} />
            </h2>
            <div style={{ marginBottom: '12px' }}>
                {(['bfs', 'dfid', 'simulate'] as const).map((m) => (
                    <label key={m} style={S.radioLabel}>
                        <input
                            type="radio"
                            name="checkingMode"
                            checked={opts.checkingMode === m}
                            onChange={() => set('checkingMode', m)}
                        />
                        {{
                            bfs: 'Model checking (BFS)',
                            dfid: 'Depth-first (DFID)',
                            simulate: 'Simulation'
                        }[m]}
                    </label>
                ))}
            </div>

            {opts.checkingMode === 'dfid' && (
                <NumberField
                    label="Max depth"
                    info={TIPS.dfidDepth}
                    value={opts.dfidDepth}
                    onChange={(v) => set('dfidDepth', v)}
                />
            )}

            {opts.checkingMode === 'simulate' && (<>
                <NumberField
                    label="Number of traces (0 = unlimited)"
                    info={TIPS.simTraces}
                    value={opts.simulateTraces}
                    onChange={(v) => set('simulateTraces', v)}
                />
                <TextField
                    label="Seed"
                    value={opts.simulateSeed}
                    placeholder="Leave empty for random"
                    onChange={(v) => set('simulateSeed', v)}
                />
            </>)}
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>RESOURCES</h2>
            <label style={S.fieldLabel}>
                Workers (threads):
                <InfoTip text={TIPS.workers} />
                <input
                    style={{ ...S.input, width: '120px' }}
                    type="number"
                    value={opts.workers}
                    min={0}
                    onChange={(e) => set('workers',
                        parseInt(e.target.value, 10) || 0
                    )}
                />
                {opts.workers === 0 && (
                    <span style={S.smallText}>
                        (0 = auto, uses all available CPU cores)
                    </span>
                )}
            </label>
            <NumberField
                label="Fingerprint bits"
                info={TIPS.fpBits}
                value={opts.fpBits}
                min={0}
                onChange={(v) => set('fpBits', v)}
            />
        </section>

        <section style={S.section}>
            <h2 style={S.sectionHeading}>ADVANCED</h2>
            <label style={S.checkbox}>
                <input
                    type="checkbox"
                    checked={opts.enableProfiling}
                    onChange={(e) => set(
                        'enableProfiling', e.target.checked
                    )}
                />
                Enable profiling
                <InfoTip text={TIPS.profiling} />
            </label>
        </section>
    </>);
}
