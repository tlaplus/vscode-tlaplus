import { VSCodeButton, VSCodeDivider, VSCodeLink } from '@vscode/webview-ui-toolkit/react';
import * as React from 'react';
import { ModelCheckResult, SpecFiles } from '../../../model/check';
import { EmptyLine } from '../common';
import { vscode } from '../vscode';

import './index.css';

interface HeaderSectionI {checkResult: ModelCheckResult}
export const HeaderSection = React.memo(({checkResult}: HeaderSectionI) => {

    const stillRunning = checkResult.state === 'R';
    const disableShowOutput = !checkResult.showFullOutput;
    const specFiles = checkResult.specFiles as SpecFiles;

    return (
        <section>
            <div className="header-title">
                <h1> Status </h1>
                <div>
                    <VSCodeButton onClick={vscode.checkAgain} appearance="primary" disabled={stillRunning}>
                        Check again
                    </VSCodeButton>
                    <VSCodeButton onClick={vscode.showTlcOutput} appearance="secondary" disabled={disableShowOutput}>
                        Full output
                    </VSCodeButton>
                </div>
            </div>

            {specFiles && <div className="spec-line"> Checking {specFiles.tlaFileName} / {specFiles.cfgFileName} </div>}

            <div className="checking-state">
                <span className={`state-${checkResult.state}`}> {checkResult.stateName} </span>
                <span hidden={checkResult.state !== 'R'}>
                    (<VSCodeLink onClick={vscode.stopProcess} href="#"> stop </VSCodeLink>)
                </span>
                <span hidden={ checkResult.statusDetails === undefined
                    || checkResult.statusDetails === null}>: {' ' + checkResult.statusDetails} </span>
            </div>

            <div className="timeInfo"> Start: {checkResult.startDateTimeStr}, end: {checkResult.endDateTimeStr} </div>

            <EmptyLine/>
            <VSCodeDivider/>
        </section>
    );
});
