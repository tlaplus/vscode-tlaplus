import { VSCodeDataGrid, VSCodeDataGridRow, VSCodePanelTab, VSCodePanelView } from '@vscode/webview-ui-toolkit/react';
import * as React from 'react';
import { InitialStateStatItem } from '../../../model/check';
import { DataGridCellDefault, DataGridCellHeader } from '../common';

interface StatesStatsI {stats: InitialStateStatItem[]}
export const StatesStats = React.memo(({stats}: StatesStatsI) => (
    <>
        <VSCodePanelTab id="stats-tab-1">States</VSCodePanelTab>
        <VSCodePanelView id="stats-view-1" className="max-width-fit-content">
            <VSCodeDataGrid aria-label="States statistics">
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
                    <VSCodeDataGridRow key={index}>
                        <DataGridCellDefault id={1} value={stat.timeStamp} alignRight={false}/>
                        <DataGridCellDefault id={2} value={stat.diameter} alignRight={true}/>
                        <DataGridCellDefault id={3} value={stat.total} alignRight={true}/>
                        <DataGridCellDefault id={4} value={stat.distinct} alignRight={true}/>
                        <DataGridCellDefault id={5} value={stat.queueSize} alignRight={true}/>
                    </VSCodeDataGridRow>)}
            </VSCodeDataGrid>
        </VSCodePanelView>
    </>
));

const headerColumns =
    [{
        value: 'Time', alignRight: false,
        tooltip: ''
    },
    {
        value: 'Diameter', alignRight: true,
        tooltip: 'The diameter of the reachable state graph'
    },
    {
        value: 'Found', alignRight: true,
        tooltip: 'The total number of states found so far'
    },
    {
        value: 'Distinct', alignRight: true,
        tooltip: 'The number of distinct states amoung all the states found'
    },
    {
        value: 'Queue', alignRight: true,
        tooltip: 'The number of states whose successor states have not been found yet'
    }];
