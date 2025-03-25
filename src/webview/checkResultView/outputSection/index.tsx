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
import { DCollection } from '../../../diagnostic';

interface OutputSectionI {checkResult: ModelCheckResult}
export const OutputSection = React.memo(({checkResult}: OutputSectionI) => {
    if (emptyOutputLines(checkResult) && emptyWarnings(checkResult) && emptyErrors(checkResult)) {
        return (null);
    }

    return (
        <section>
            <VSCodePanels id="output-panels">
            {!emptyErrors(checkResult) &&
                    <>
                        <VSCodePanelTab id="output-tab-1"> Errors </VSCodePanelTab>
                        <VSCodePanelView id="output-view-1" className="flex-direction-column">
                            {checkResult.errors.map((error: ErrorInfo, errorId: number) => (
                                <div key={errorId} className="margin-0">
                                    {error.lines.map((v, index) => (
                                        <MessageLineSpan sanyMessages={checkResult.sanyMessages}
                                            key={index} message={v}/>))}
                                    <ErrorLink error={error} index={errorId}/>
                                </div>))
                            }
                        </VSCodePanelView>
                    </>}
                {!emptyOutputLines(checkResult) &&
                    <>
                        <VSCodePanelTab id="output-tab-2"> Output </VSCodePanelTab>
                        <VSCodePanelView id="output-view-2" className="flex-direction-column">
                            {checkResult.outputLines.map((v, index) => <OutputLineElement key={index} line={v}/>)}
                        </VSCodePanelView>
                    </>}

                {!emptyWarnings(checkResult) &&
                    <>
                        <VSCodePanelTab id="output-tab-3"> Warnings </VSCodePanelTab>
                        <VSCodePanelView id="output-view-3" className="flex-direction-column">
                            {checkResult.warnings.map((warning: WarningInfo, warningId: number) => (
                                <p key={warningId} className="margin-0">
                                    {warning.lines.map((v, index) =>(
                                        <MessageLineSpan sanyMessages={checkResult.sanyMessages}
                                            key={index} message={v}/>))}
                                </p>))
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

interface MessageLineSpanI { message: MessageLine, sanyMessages: DCollection | undefined }
const MessageLineSpan = React.memo(({ message, sanyMessages }: MessageLineSpanI) =>
    (<p className="margin-0">
        {message.spans.map((span, index) => {
            const dmsg = sanyMessages?.messages?.find((v) => v.diagnostic.message === span.text);
            const position = span.location || dmsg?.position;
            const filePath = span.filePath || dmsg?.filePath;
            return (
                <CodePositionLink key={index} line={span.text} filepath={filePath} position={position} />
            );
        }
        )}
    </p>));

export function emptyOutputLines(checkResult: ModelCheckResult) {
    return !checkResult.outputLines || checkResult.outputLines.length === 0;
}

export function emptyWarnings(checkResult: ModelCheckResult) {
    return !checkResult.warnings || checkResult.warnings.length === 0;
}

export function emptyErrors(checkResult: ModelCheckResult) {
    return !checkResult.errors || checkResult.errors.length === 0;
}
