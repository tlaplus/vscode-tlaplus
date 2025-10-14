import {
    VscodeTabHeader,
    VscodeTabPanel,
    VscodeTextfield,
    VscodeTree
} from '@vscode-elements/react-elements';
import * as React from 'react';
import { ErrorInfo } from '../../../model/check';
import { ErrorTraceState } from './errorTraceState';
import { createTreeItemRegistry, TreeItemRegistry } from './treeItemRegistry';

type TextfieldElement = HTMLElementTagNameMap['vscode-textfield'];

interface ErrorTraceI {errorInfo: ErrorInfo, traceId: number}
export const ErrorTrace = React.memo(({errorInfo, traceId}: ErrorTraceI) => {
    if (!errorInfo.errorTrace || errorInfo.errorTrace.length === 0) {
        return (null);
    }

    const {
        settings,
        registerStateTreeItem,
        setHideModified,
        setFilter,
        collapseAllStates,
        expandAllStates
    } = useSettings();

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
                                stateIndex={index}
                                errorTraceItem={v}
                                settings={settings}
                                registerTreeItem={registerStateTreeItem}/>)}
                </VscodeTree>
            </VscodeTabPanel>
        </>
    );
});

export interface ErrorTraceSettings {
    readonly hideModified: boolean;
    readonly filter: string[];
}

type StateTreeItem = HTMLElementTagNameMap['vscode-tree-item'];

const useSettings = () => {
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
    const stateTreeItems = React.useRef<TreeItemRegistry<StateTreeItem>>(createTreeItemRegistry<StateTreeItem>());

    const setFilter = (newFilter: string) => {
        _setFilter(parseFilter(newFilter));
    };

    const setHideModified = (newHideModified: boolean) => {
        _setHideModified(newHideModified);
    };

    const registerStateTreeItem = React.useCallback((index: number, item: StateTreeItem | null) => {
        stateTreeItems.current.register(index, item);
    }, []);

    const collapseAllStates = React.useCallback(() => {
        stateTreeItems.current.collapseAll();
    }, []);

    const expandAllStates = React.useCallback(() => {
        stateTreeItems.current.expandAll();
    }, []);

    const settings = { hideModified: hideModified, filter: filter };
    return {
        settings,
        registerStateTreeItem,
        setHideModified,
        setFilter,
        collapseAllStates,
        expandAllStates
    };
};
