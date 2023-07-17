import { VSCodeDataGrid, VSCodeDataGridRow, VSCodePanelTab, VSCodePanelView } from '@vscode/webview-ui-toolkit/react';
import * as React from 'react';
import { CoverageItem } from '../../../model/check';
import { CodeRangeLink, DataGridCellDefault, DataGridCellHeader } from '../common';

interface CoverageStatsI {stats: CoverageItem[]}
export const CoverageStats = React.memo(({stats}: CoverageStatsI) => {
    const tooltip = (stat: CoverageItem) =>
        stat.total !== 0 ? '' : 'This action has never been used to compute successor states';

    const codeLink = (stat: CoverageItem) =>
        <CodeRangeLink line={stat.action} filepath={stat.filePath} range={stat.range}/>;

    return (<>
        <VSCodePanelTab id="stats-tab-2"> Coverage </VSCodePanelTab>
        <VSCodePanelView id="stats-view-2" className="max-width-fit-content">
            <VSCodeDataGrid aria-label="Coverage statistics">
                <VSCodeDataGridRow rowType="sticky-header">
                    {headerColumns.map((v, id) =>
                        <DataGridCellHeader
                            key={id}
                            id={id+1}
                            value={v.value}
                            alignRight={v.alignRight}
                            tooltip={v.tooltip}/>)}
                </VSCodeDataGridRow>

                {stats.map((stat, index) =>
                    <VSCodeDataGridRow key={index} className={stat.total !== 0 ? '' : 'coverage-zero'}>
                        <DataGridCellDefault id={1} value={stat.module} alignRight={false} tooltip={tooltip(stat)}/>
                        <DataGridCellDefault id={2} value={codeLink(stat)} alignRight={false} tooltip={tooltip(stat)}/>
                        <DataGridCellDefault id={3} value={stat.total} alignRight={true} tooltip={tooltip(stat)}/>
                        <DataGridCellDefault id={4} value={stat.distinct} alignRight={true} tooltip={tooltip(stat)}/>
                    </VSCodeDataGridRow>)}
            </VSCodeDataGrid>
        </VSCodePanelView>
    </>
    );
});

const headerColumns =
    [{
        value: 'Module', alignRight: false,
        tooltip: ''
    },
    {
        value: 'Action', alignRight: false,
        tooltip: ''
    },
    {
        value: 'Total', alignRight: true,
        tooltip: 'Total number of times the action has been used to compute a successor state'
    },
    {
        value: 'Distinct', alignRight: true,
        tooltip: 'Total number of times the action produced a distinct successor state'
    }];
