import { VSCodePanels } from '@vscode/webview-ui-toolkit/react';
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
            <VSCodePanels id="error-trace-panels">
                {checkResult.errors.map((error, index) => <ErrorTrace key={index} errorInfo={error} traceId={index}/>)}
            </VSCodePanels>
        </section>
    );
});
