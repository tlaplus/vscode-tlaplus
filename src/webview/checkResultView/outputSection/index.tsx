import { Panels } from '@vscode/webview-ui-toolkit';
import {
    VSCodeDivider,
    VSCodeLink,
    VSCodePanelTab,
    VSCodePanelView,
    VSCodePanels
} from '@vscode/webview-ui-toolkit/react';
import * as React from 'react';
import { ErrorInfo, MessageLine, ModelCheckResult, OutputLine, WarningInfo } from '../../../model/check';
import { CodePositionLink } from '../common';

import './index.css';

interface OutputSectionI {checkResult: ModelCheckResult}
export const OutputSection = React.memo(({checkResult}: OutputSectionI) => {
    if (emptyOutputLines(checkResult) && emptyWarnings(checkResult) && emptyErrors(checkResult)) {
        return (null);
    }

    return (
        <section>
            <VSCodePanels id="output-panels">
                {!emptyOutputLines(checkResult) &&
                    <>
                        <VSCodePanelTab id="output-tab-1"> Output </VSCodePanelTab>
                        <VSCodePanelView id="output-view-1" className="flex-direction-column">
                            {checkResult.outputLines.map((v, index) => <OutputLineElement key={index} line={v}/>)}
                        </VSCodePanelView>
                    </>}

                {!emptyWarnings(checkResult) &&
                    <>
                        <VSCodePanelTab id="output-tab-2"> Warnings </VSCodePanelTab>
                        <VSCodePanelView id="output-view-2" className="flex-direction-column">
                            {checkResult.warnings.map((warning: WarningInfo, warningId: number) => (
                                <p key={warningId} className="margin-0">
                                    {warning.lines.map((v, index) => <MessageLineSpan key={index} message={v}/>)}
                                </p>))
                            }
                        </VSCodePanelView>
                    </>}

                {!emptyErrors(checkResult) &&
                    <>
                        <VSCodePanelTab id="output-tab-3"> Errors </VSCodePanelTab>
                        <VSCodePanelView id="output-view-3" className="flex-direction-column">
                            {checkResult.errors.map((error: ErrorInfo, errorId: number) => (
                                <div key={errorId} className="margin-0">
                                    {error.lines.map((v, index) => <MessageLineSpan key={index} message={v}/>)}
                                    <ErrorLink error={error} index={errorId}/>
                                </div>))
                            }
                        </VSCodePanelView>
                    </>}
            </VSCodePanels>
            <VSCodeDivider/>
        </section>
    );
});

interface OutputLineElementI {line: OutputLine}
const OutputLineElement = React.memo(({line}: OutputLineElementI) => {
    if (line.count === 1) {
        return (<p className="margin-0"> {line.text} </p>);
    }

    return (
        <p className="margin-0">
            <span> {line.text} </span>
            <span className="opacity-50" title="Number of consecutive occurrences"> ({line.count}) </span>
        </p>
    );
});

interface ErrorLinkI {error: ErrorInfo, index: number}
const ErrorLink = React.memo(({error, index}: ErrorLinkI) => {
    if (error.errorTrace === null || error.errorTrace.length === 0) {
        return (null);
    }

    const switchTab = () => {
        const panels = document.getElementById('error-trace-panels') as Panels;
        panels.activeid = 'error-trace-tab-' + index;
    };
    return (
        <VSCodeLink onClick={switchTab} href="#error-trace-panels"> Show error trace </VSCodeLink>
    );
});

interface MessageLineSpanI {message: MessageLine}
const MessageLineSpan = React.memo(({message}: MessageLineSpanI) => (
    <p className="margin-0">
        {message.spans.map((span, index) => (
            span.type !== 'SL' ?
                <span key={index}> {span.text} </span> :
                <CodePositionLink key={index} line={span.text} filepath={span.filePath} position={span.location}/>
        ))}
    </p>
));

export function emptyOutputLines(checkResult: ModelCheckResult) {
    return !checkResult.outputLines || checkResult.outputLines.length === 0;
}

export function emptyWarnings(checkResult: ModelCheckResult) {
    return !checkResult.warnings || checkResult.warnings.length === 0;
}

export function emptyErrors(checkResult: ModelCheckResult) {
    return !checkResult.errors || checkResult.errors.length === 0;
}
