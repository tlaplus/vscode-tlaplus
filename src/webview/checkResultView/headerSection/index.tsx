import { VscodeButton, VscodeDivider } from '@vscode-elements/react-elements';
import * as React from 'react';
import { ModelCheckResult, SpecFiles } from '../../../model/check';
import { EmptyLine, VSCodeLink } from '../common';
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
                    <VscodeButton onClick={vscode.checkAgain} disabled={stillRunning}>
                        Check again
                    </VscodeButton>
                    <VscodeButton secondary onClick={vscode.showTlcOutput} disabled={disableShowOutput}>
                        Full output
                    </VscodeButton>
                </div>
            </div>

            {specFiles && <div className="spec-line"> Checking {specFiles.tlaFileName} / {specFiles.cfgFileName} </div>}

            <div className="checking-state">
                <span className={`state-${checkResult.state}`}> {checkResult.stateName} </span>
                <span hidden={checkResult.state !== 'R'}>
                    (<VSCodeLink onClick={vscode.stopProcess}> stop </VSCodeLink>)
                </span>
                <span hidden={ checkResult.statusDetails === undefined
                    || checkResult.statusDetails === null}>: {' ' + checkResult.statusDetails} </span>
            </div>

            <div className="timeInfo"> Start: {checkResult.startDateTimeStr}, end: {checkResult.endDateTimeStr} </div>

            <EmptyLine/>
            <VscodeDivider/>
        </section>
    );
});
