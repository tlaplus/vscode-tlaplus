import {
    VscodeTabHeader,
    VscodeTabPanel,
    VscodeTextfield,
    VscodeTree
} from '@vscode-elements/react-elements';
import * as React from 'react';
import { ErrorInfo } from '../../../model/check';
import { ErrorTraceState } from './errorTraceState';

type TextfieldElement = HTMLElementTagNameMap['vscode-textfield'];

interface ErrorTraceI {errorInfo: ErrorInfo, traceId: number}
export const ErrorTrace = React.memo(({errorInfo, traceId}: ErrorTraceI) => {
    if (!errorInfo.errorTrace || errorInfo.errorTrace.length === 0) {
        return (null);
    }

    const {settings, expandedStates, setHideModified, setFilter, collapseAllStates, expandAllStates} =
        useSettings(errorInfo.errorTrace.length);

    const handleFilterChange = (event: React.ChangeEvent<TextfieldElement>) => {
        setFilter(event.currentTarget.value);
    };

    const handleFilterIconClick = (event: React.MouseEvent<HTMLSpanElement>) => {
        const field = event.currentTarget.closest('vscode-textfield') as TextfieldElement | null;
        if (field) {
            setFilter(field.value);
        }
    };

    return (
        <>
            <VscodeTabHeader slot="header">Counterexample {traceId}</VscodeTabHeader>
            <VscodeTabPanel panel className="flex-direction-column panel-padding">
                <div className="error-trace-options">
                    <VscodeTextfield onChange={handleFilterChange} placeholder="Filter">
                        <span
                            slot="content-after"
                            className="codicon codicon-search cursor-pointer"
                            onClick={handleFilterIconClick}/>
                    </VscodeTextfield>

                    {settings.hideModified &&
                        <span
                            title="Show unmodified variables"
                            onClick={() => setHideModified(false)}
                            className="codicon codicon-eye cursor-pointer option-button"/>}

                    {!settings.hideModified &&
                        <span
                            title="Hide unmodified variables"
                            onClick={() => setHideModified(true)}
                            className="codicon codicon-eye-closed cursor-pointer option-button"/>}

                    <span
                        title="Collapse all states"
                        onClick={collapseAllStates}
                        className="codicon codicon-fold cursor-pointer option-button"/>

                    <span
                        title="Expand all states"
                        onClick={expandAllStates}
                        className="codicon codicon-unfold cursor-pointer option-button"/>

                </div>

                <VscodeTree>
                    {errorInfo.errorTrace.map(
                        (v, index) =>
                            <ErrorTraceState
                                key={index}
                                errorTraceItem={v}
                                settings={settings}
                                expanded={expandedStates[index]}/>)}
                </VscodeTree>
            </VscodeTabPanel>
        </>
    );
});

export interface ErrorTraceSettings {
    readonly hideModified: boolean;
    readonly filter: string[];
    setExpandValue: (index: number, newValue: boolean) => void;
}

const useSettings = (numberOfStates: number) => {
    function parseFilter(filter: string): string[] {
        return !filter ? [] :
            filter
                .trim()
                .split(/\s|,/g)
                .filter(p => p !== '')
                .map(p => p.toLowerCase());
    }

    const [hideModified, _setHideModified] = React.useState(false);
    const [filter, _setFilter] = React.useState(parseFilter(''));
    const [expandedStates, _setExpandStates] = React.useState(new Array(numberOfStates).fill(true));

    const setFilter = (newFilter: string) => {
        _setFilter(parseFilter(newFilter));
    };

    const setHideModified = (newHideModified: boolean) => {
        _setHideModified(newHideModified);
    };

    const setExpandValue = (index: number, newValue: boolean) => {
        if (newValue !== expandedStates[index]) {
            const newValueArray = [...expandedStates];
            newValueArray[index] = newValue;
            _setExpandStates(newValueArray);
        }
    };

    const collapseAllStates = () => {
        _setExpandStates(new Array(numberOfStates).fill(false));
    };

    const expandAllStates = () => {
        _setExpandStates(new Array(numberOfStates).fill(true));
    };

    const settings = { hideModified: hideModified, filter: filter, setExpandValue: setExpandValue};
    return {settings, expandedStates, setHideModified, setFilter, collapseAllStates, expandAllStates};
};
