import * as vscode from 'vscode';
import {
    CMD_REFRESH_TLC_COVERAGE_INSPECTOR,
    CMD_REVEAL_TLC_COVERAGE_ENTRY,
    CMD_SHOW_TLC_COVERAGE_INSPECTOR,
    revealCoverageEntry,
    TlcCoverageInspectorTreeDataProvider
} from '../panels/tlcCoverageInspectorTreeDataProvider';
import { TlcCoverageDecorationProvider } from '../tlcCoverage';

export const CMD_TOGGLE_COVERAGE = 'tlaplus.tlc.profiler.toggle';
export const CMD_CLEAR_COVERAGE = 'tlaplus.tlc.profiler.clear';

let statusBarItem: vscode.StatusBarItem | undefined;

export function registerCoverageCommands(
    context: vscode.ExtensionContext,
    provider: TlcCoverageDecorationProvider,
    inspectorProvider: TlcCoverageInspectorTreeDataProvider
): void {
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    context.subscriptions.push(statusBarItem);

    context.subscriptions.push(
        vscode.commands.registerCommand(CMD_TOGGLE_COVERAGE, () => {
            const newState = !provider.isEnabled();
            provider.setEnabled(newState);
            updateStatusBar(newState);
            const message = newState
                ? 'TLC source coverage heatmap enabled'
                : 'TLC source coverage heatmap disabled';
            vscode.window.showInformationMessage(message);
        }),
        vscode.commands.registerCommand(CMD_CLEAR_COVERAGE, () => {
            provider.clearCoverage();
            inspectorProvider.refresh();
            vscode.window.showInformationMessage('TLC coverage data cleared');
        }),
        vscode.commands.registerCommand(CMD_SHOW_TLC_COVERAGE_INSPECTOR, () =>
            vscode.commands.executeCommand(`${TlcCoverageInspectorTreeDataProvider.viewType}.focus`)
        ),
        vscode.commands.registerCommand(CMD_REFRESH_TLC_COVERAGE_INSPECTOR, () => {
            inspectorProvider.refresh();
        }),
        vscode.commands.registerCommand(CMD_REVEAL_TLC_COVERAGE_ENTRY, (entry) => revealCoverageEntry(entry))
    );

    updateStatusBar(provider.isEnabled());
}

function updateStatusBar(enabled: boolean): void {
    if (!statusBarItem) {
        return;
    }

    if (enabled) {
        statusBarItem.text = '$(flame) TLC Coverage';
        statusBarItem.tooltip = 'TLC source coverage heatmap is active. Click to disable.';
    } else {
        statusBarItem.text = '$(flame) TLC Coverage (off)';
        statusBarItem.tooltip = 'TLC source coverage heatmap is disabled. Click to enable.';
    }
    statusBarItem.command = CMD_TOGGLE_COVERAGE;
    statusBarItem.show();
}
