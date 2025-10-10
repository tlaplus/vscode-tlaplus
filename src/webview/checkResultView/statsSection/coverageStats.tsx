import {
    VscodeTabHeader,
    VscodeTabPanel,
    VscodeTable,
    VscodeTableBody,
    VscodeTableHeader,
    VscodeTableRow
} from '@vscode-elements/react-elements';
import * as React from 'react';
import { CoverageItem } from '../../../model/check';
import { CodeRangeLink, DataGridCellDefault, DataGridCellHeader } from '../common';

interface CoverageStatsI {stats: CoverageItem[]}
export const CoverageStats = React.memo(({stats}: CoverageStatsI) => {
    const tooltip = (stat: CoverageItem) =>
        stat.total !== 0 ? '' : 'This action has never been used to compute successor states';

    const codeLink = (stat: CoverageItem) =>
        <CodeRangeLink line={stat.action} filepath={stat.filePath} range={stat.range}/>;

    return (
        <>
            <VscodeTabHeader slot="header">Coverage</VscodeTabHeader>
            <VscodeTabPanel panel className="max-width-fit-content">
                <VscodeTable aria-label="Coverage statistics" borderedRows responsive>
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
                            <VscodeTableRow key={index} className={stat.total !== 0 ? '' : 'coverage-zero'}>
                                <DataGridCellDefault value={stat.module} alignRight={false} tooltip={tooltip(stat)}/>
                                <DataGridCellDefault value={codeLink(stat)} alignRight={false} tooltip={tooltip(stat)}/>
                                <DataGridCellDefault value={stat.total} alignRight={true} tooltip={tooltip(stat)}/>
                                <DataGridCellDefault value={stat.distinct} alignRight={true} tooltip={tooltip(stat)}/>
                            </VscodeTableRow>)}
                    </VscodeTableBody>
                </VscodeTable>
            </VscodeTabPanel>
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
