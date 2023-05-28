import { VSCodeDivider, VSCodePanels } from '@vscode/webview-ui-toolkit/react';
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
            <VSCodePanels>
                <StatesStats stats={checkResult.initialStatesStat}/>
                <CoverageStats stats={checkResult.coverageStat}/>
            </VSCodePanels>
            <EmptyLine/>
            <VSCodeDivider/>
        </section>
    );
});
