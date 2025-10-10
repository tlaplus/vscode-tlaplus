import {
    VscodeTabHeader,
    VscodeTabPanel,
    VscodeTable,
    VscodeTableBody,
    VscodeTableHeader,
    VscodeTableRow
} from '@vscode-elements/react-elements';
import * as React from 'react';
import { InitialStateStatItem } from '../../../model/check';
import { DataGridCellDefault, DataGridCellHeader } from '../common';

interface StatesStatsI {stats: InitialStateStatItem[]}
export const StatesStats = React.memo(({stats}: StatesStatsI) => (
    <>
        <VscodeTabHeader slot="header">States</VscodeTabHeader>
        <VscodeTabPanel panel className="max-width-fit-content">
            <VscodeTable aria-label="States statistics" borderedRows responsive>
                <VscodeTableHeader>
                    <VscodeTableRow>
                        {headerColumns.map((v, id) =>
                            <DataGridCellHeader
                                key={id}
                                value={v.value}
                                alignRight={v.alignRight}
                                tooltip={v.tooltip}/>)}
                    </VscodeTableRow>
                </VscodeTableHeader>

                <VscodeTableBody>
                    {stats.map((stat, index) =>
                        <VscodeTableRow key={index}>
                            <DataGridCellDefault value={stat.timeStamp} alignRight={false}/>
                            <DataGridCellDefault value={stat.diameter} alignRight={true}/>
                            <DataGridCellDefault value={stat.total} alignRight={true}/>
                            <DataGridCellDefault value={stat.distinct} alignRight={true}/>
                            <DataGridCellDefault value={stat.queueSize} alignRight={true}/>
                        </VscodeTableRow>)}
                </VscodeTableBody>
            </VscodeTable>
        </VscodeTabPanel>
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
