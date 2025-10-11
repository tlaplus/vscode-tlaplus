import {
    VscodeDivider,
    VscodeTabHeader,
    VscodeTabPanel,
    VscodeTabs
} from '@vscode-elements/react-elements';
import * as React from 'react';
import { ErrorInfo, MessageLine, ModelCheckResult, OutputLine, WarningInfo } from '../../../model/check';
import { CodePositionLink, VSCodeLink } from '../common';

import './index.css';
import { DCollection } from '../../../diagnostic';

type VscodeTabsElement = HTMLElementTagNameMap['vscode-tabs'];

interface OutputSectionI {checkResult: ModelCheckResult}
export const OutputSection = React.memo(({checkResult}: OutputSectionI) => {
    if (emptyOutputLines(checkResult) && emptyWarnings(checkResult) && emptyErrors(checkResult)) {
        return (null);
    }

    return (
        <section>
            <VscodeTabs id="output-tabs" panel>
                {!emptyErrors(checkResult) &&
                    <>
                        <VscodeTabHeader slot="header">Errors</VscodeTabHeader>
                        <VscodeTabPanel panel className="flex-direction-column panel-padding">
                            {checkResult.errors.map((error: ErrorInfo, errorId: number) => (
                                <div key={errorId} className="margin-0">
                                    {error.lines.map((v, index) => (
                                        <MessageLineSpan sanyMessages={checkResult.sanyMessages}
                                            key={index} message={v}/>))}
                                    <ErrorLink error={error} index={errorId}/>
                                </div>))
                            }
                        </VscodeTabPanel>
                    </>}
                {!emptyOutputLines(checkResult) &&
                    <>
                        <VscodeTabHeader slot="header">Output</VscodeTabHeader>
                        <VscodeTabPanel panel className="flex-direction-column panel-padding">
                            {checkResult.outputLines.map((v, index) => <OutputLineElement key={index} line={v}/>)}
                        </VscodeTabPanel>
                    </>}

                {!emptyWarnings(checkResult) &&
                    <>
                        <VscodeTabHeader slot="header">Warnings</VscodeTabHeader>
                        <VscodeTabPanel panel className="flex-direction-column panel-padding">
                            {checkResult.warnings.map((warning: WarningInfo, warningId: number) => (
                                <p key={warningId} className="margin-0">
                                    {warning.lines.map((v, index) =>(
                                        <MessageLineSpan sanyMessages={checkResult.sanyMessages}
                                            key={index} message={v}/>))}
                                </p>))
                            }
                        </VscodeTabPanel>
                    </>}
            </VscodeTabs>
            <VscodeDivider/>
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
        const tabs = document.getElementById('error-trace-tabs') as VscodeTabsElement | null;
        if (tabs) {
            tabs.selectedIndex = index;
            tabs.focus();
        }
    };
    return (
        <VSCodeLink onClick={switchTab}> Show error trace </VSCodeLink>
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
