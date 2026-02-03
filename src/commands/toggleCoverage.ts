import * as vscode from 'vscode';
import { TlcCoverageDecorationProvider } from '../tlcCoverage';

export const CMD_TOGGLE_COVERAGE = 'tlaplus.tlc.profiler.toggle';
export const CMD_CLEAR_COVERAGE = 'tlaplus.tlc.profiler.clear';

let statusBarItem: vscode.StatusBarItem | undefined;

export function registerCoverageCommands(
    context: vscode.ExtensionContext,
    provider: TlcCoverageDecorationProvider
): void {
    // Create status bar item
    statusBarItem = vscode.window.createStatusBarItem(
        vscode.StatusBarAlignment.Right,
        100
    );
    context.subscriptions.push(statusBarItem);
    context.subscriptions.push(
        provider.onDidChangeEnabled((enabled) => updateStatusBar(enabled))
    );

    context.subscriptions.push(
        vscode.commands.registerCommand(CMD_TOGGLE_COVERAGE, () => {
            const newState = !provider.isEnabled();
            provider.setEnabled(newState);
            updateStatusBar(newState);

            const message = newState
                ? 'TLC coverage visualization enabled'
                : 'TLC coverage visualization disabled';
            vscode.window.showInformationMessage(message);
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand(CMD_CLEAR_COVERAGE, () => {
            provider.clearCoverage();
            vscode.window.showInformationMessage('TLC coverage data cleared');
        })
    );

    // Initialize status bar
    updateStatusBar(provider.isEnabled());
}

function updateStatusBar(enabled: boolean) {
    if (!statusBarItem) {return;}

    if (enabled) {
        statusBarItem.text = '$(flame) Coverage';
        statusBarItem.tooltip = 'TLC coverage visualization is active. Click to disable.';
    } else {
        statusBarItem.text = '$(flame) Coverage (off)';
        statusBarItem.tooltip = 'TLC coverage visualization is disabled. Click to enable.';
    }
    statusBarItem.command = CMD_TOGGLE_COVERAGE;
    statusBarItem.show();
}
