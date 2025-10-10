import { VscodeDivider, VscodeTabs } from '@vscode-elements/react-elements';
import * as React from 'react';
import { ModelCheckResult } from '../../../model/check';
import { EmptyLine } from '../common';
import { CoverageStats } from './coverageStats';
import { StatesStats } from './statesStats';

import './index.css';

interface StatsSectionI {checkResult: ModelCheckResult}
export const StatsSection = React.memo(({checkResult}: StatsSectionI) => {
    return (
        <section>
            <VscodeTabs panel>
                <StatesStats stats={checkResult.initialStatesStat}/>
                {checkResult.coverageStat.length > 0 && <CoverageStats stats={checkResult.coverageStat}/>}
            </VscodeTabs>
            <EmptyLine/>
            <VscodeDivider/>
        </section>
    );
});
