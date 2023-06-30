import { treeItemStyles as fastTreeItemStyles } from '@microsoft/fast-components';
import { ElementStyles, css } from '@microsoft/fast-element';
import {
    ElementDefinitionContext,
    FoundationElementTemplate,
    OverrideFoundationElementDefinition,
    TreeItemOptions
} from '@microsoft/fast-foundation';

/*
*  Selected all classes from original template (e.g. treeItemStyles, look into compiled js)
*  that had the following properties to override: background, color, heigh.
*
*  The vscode color variables were inspired by the ones used in the toolkit:
*  https://github.com/microsoft/vscode-webview-ui-toolkit/blob/main/src/design-tokens.ts
*/
export const treeItemStyles: FoundationElementTemplate<ElementStyles, TreeItemOptions> =
    (context: ElementDefinitionContext, definition: OverrideFoundationElementDefinition<TreeItemOptions>) =>
        css`
            ${fastTreeItemStyles(context, definition)}

            :host,
            .positioning-region,
            .expand-collapse-button {
                background: transparent;
                color: var(--vscode-foreground);
            }

            :host(:not([disabled])) .positioning-region,
            :host([selected]) .positioning-region,
            :host([selected])::after {
                background: transparent;
                color: var(--vscode-foreground);
            }

            :host(:not([disabled])) .positioning-region:active,
            :host([selected]:not([disabled])) .positioning-region:active {
                background: transparent;
                color: var(--vscode-foreground);
            }

            :host(:not([disabled])) .positioning-region:hover,
            :host(.nested:not([disabled])) .expand-collapse-button:hover,
            :host([selected]:not([disabled])) .positioning-region:hover,
            :host([selected]:not([disabled])) .expand-collapse-button:hover {
                background: var(--vscode-list-hoverBackground);
                color: var(--vscode-foreground);
            }

            .positioning-region, .content-region, .expand-collapse-button, .expand-collapse-glyph {
                height: fit-content;
            }

            .content-region {
                display: grid;
            }
        `;
