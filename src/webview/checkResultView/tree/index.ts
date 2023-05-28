import { provideFASTDesignSystem, treeViewStyles } from '@microsoft/fast-components';
import {
    FoundationElementDefinition,
    TreeItem as FoundationTreeItem,
    TreeView as FoundationTreeView,
    TreeItemOptions,
    treeItemTemplate,
    treeViewTemplate
} from '@microsoft/fast-foundation';
import { provideReactWrapper } from '@microsoft/fast-react-wrapper';
import * as React from 'react';
import { treeItemStyles } from './tree-item.styles';

const {wrap} = provideReactWrapper(React, provideFASTDesignSystem());

// Tree View

class TreeView extends FoundationTreeView {}

const vsCodeTreeView = TreeView.compose<FoundationElementDefinition, typeof TreeView>({
    baseName: 'tree-view',
    baseClass: FoundationTreeView,
    template: treeViewTemplate,
    styles: treeViewStyles
});

export const VSCodeTreeView = wrap(vsCodeTreeView());

// Tree Item

class TreeItem extends FoundationTreeItem {}

const vsCodeTreeItem = TreeItem.compose<TreeItemOptions, typeof TreeItem>({
    baseName: 'tree-item',
    baseClass: FoundationTreeItem,
    template: treeItemTemplate,
    styles: treeItemStyles,
    expandCollapseGlyph: `
        <svg viewBox="0 0 16 16" xmlns="http://www.w3.org/2000/svg" class="expand-collapse-glyph">
            <path d="M5 12.3a1 1 0 0 0 1.6.8L11 8.8a1.5 1.5 0 0 0 0-2.3L6.6 2.2A1 1 0 0 0 5 3v9.3Z"/>
        </svg>
    `,
});

export const VSCodeTreeItem = wrap(vsCodeTreeItem(), {
    events: {
        onExpandedChanged: 'expanded-change'
    }
});

