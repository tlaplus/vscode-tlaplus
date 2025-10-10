import { VscodeTabs } from '@vscode-elements/react-elements';
import * as React from 'react';
import { ModelCheckResult } from '../../../model/check';
import { ErrorTrace } from './errorTrace';

import './index.css';

interface ErrorTraceSectionI {checkResult: ModelCheckResult}
export const ErrorTraceSection = React.memo(({checkResult}: ErrorTraceSectionI) => {
    if (!checkResult.errors || checkResult.errors.length === 0) {
        return (null);
    }

    return (
        <section>
            <VscodeTabs id="error-trace-tabs" panel>
                {checkResult.errors.map((error, index) => <ErrorTrace key={index} errorInfo={error} traceId={index}/>)}
            </VscodeTabs>
        </section>
    );
});
