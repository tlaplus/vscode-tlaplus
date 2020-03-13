import * as vscode from 'vscode';
import * as path from 'path';
import { CMD_CHECK_MODEL_RUN, CMD_CHECK_MODEL_STOP, CMD_CHECK_MODEL_DISPLAY, CMD_SHOW_TLC_OUTPUT,
    CMD_CHECK_MODEL_CUSTOM_RUN, checkModel, displayModelChecking, stopModelChecking,
    showTlcOutput, checkModelCustom, CMD_CHECK_MODEL_RUN_AGAIN, runLastCheckAgain} from './commands/checkModel';
import { CMD_EVALUATE_SELECTION, evaluateSelection, CMD_EVALUATE_EXPRESSION,
    evaluateExpression } from './commands/evaluateExpression';
import { showModelEditor, CMD_MODEL_EDITOR_DISPLAY } from './modelEditorView';
import { parseModule, CMD_PARSE_MODULE } from './commands/parseModule';
import { visualizeTlcOutput, CMD_VISUALIZE_TLC_OUTPUT } from './commands/visualizeOutput';
import { exportModuleToTex, exportModuleToPdf, CMD_EXPORT_TLA_TO_TEX,
    CMD_EXPORT_TLA_TO_PDF } from './commands/exportModule';
import { TlaOnTypeFormattingEditProvider } from './formatters/tla';
import { CfgOnTypeFormattingEditProvider } from './formatters/cfg';
import { TlaCodeActionProvider } from './actions';
import { TlaDocumentSymbolsProvider } from './symbols/tlaSymbols';
import { LANG_TLAPLUS, LANG_TLAPLUS_CFG, exists, readFile, writeFile } from './common';
import { TlaCompletionItemProvider } from './completions/tlaCompletions';
import { CfgCompletionItemProvider } from './completions/cfgCompletions';
import { TlaDeclarationsProvider, TlaDefinitionsProvider } from './declarations/tlaDeclarations';
import { TlaDocumentInfos } from './model/documentInfo';
import { syncTlcStatisticsSetting, listenTlcStatConfigurationChanges } from './commands/tlcStatisticsCfg';

const TLAPLUS_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS };
const TLAPLUS_CFG_FILE_SELECTOR: vscode.DocumentSelector = { scheme: 'file', language: LANG_TLAPLUS_CFG };
const CHANGELOG_URL = vscode.Uri.parse('https://github.com/alygin/vscode-tlaplus/blob/master/CHANGELOG.md#change-log');

const tlaDocInfos = new TlaDocumentInfos();
export const symbolsProvider = new TlaDocumentSymbolsProvider(tlaDocInfos);

// Holds all the error messages
let diagnostic: vscode.DiagnosticCollection;

/**
 * Extension entry point.
 */
export function activate(context: vscode.ExtensionContext) {
    diagnostic = vscode.languages.createDiagnosticCollection(LANG_TLAPLUS);
    context.subscriptions.push(
        vscode.commands.registerCommand(
            CMD_PARSE_MODULE,
            () => parseModule(diagnostic)),
        vscode.commands.registerCommand(
            CMD_EXPORT_TLA_TO_TEX,
            () => exportModuleToTex(context)),
        vscode.commands.registerCommand(
            CMD_EXPORT_TLA_TO_PDF,
            () => exportModuleToPdf(context)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_RUN,
            (uri) => checkModel(uri, diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_RUN_AGAIN,
            () => runLastCheckAgain(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_CUSTOM_RUN,
            () => checkModelCustom(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_SHOW_TLC_OUTPUT,
            () => showTlcOutput()),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_STOP,
            () => stopModelChecking()),
        vscode.commands.registerCommand(
            CMD_CHECK_MODEL_DISPLAY,
            () => displayModelChecking(context)),
        vscode.commands.registerCommand(
            CMD_MODEL_EDITOR_DISPLAY,
            () => showModelEditor(context)),
        vscode.commands.registerCommand(
            CMD_VISUALIZE_TLC_OUTPUT,
            () => visualizeTlcOutput(context)),
        vscode.commands.registerCommand(
            CMD_EVALUATE_SELECTION,
            () => evaluateSelection(diagnostic, context)),
        vscode.commands.registerCommand(
            CMD_EVALUATE_EXPRESSION,
            () => evaluateExpression(diagnostic, context)),
        vscode.languages.registerCodeActionsProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaCodeActionProvider(),
            { providedCodeActionKinds: [ vscode.CodeActionKind.Source ] }),
        vscode.languages.registerOnTypeFormattingEditProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaOnTypeFormattingEditProvider(),
            '\n', 'd', 'e', 'f', 'r'),
        vscode.languages.registerOnTypeFormattingEditProvider(
            TLAPLUS_CFG_FILE_SELECTOR,
            new CfgOnTypeFormattingEditProvider(),
            '\n'),
        vscode.languages.registerDocumentSymbolProvider(
            TLAPLUS_FILE_SELECTOR,
            symbolsProvider,
            { label: 'TLA+' }),
        vscode.languages.registerCompletionItemProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaCompletionItemProvider(tlaDocInfos)),
        vscode.languages.registerCompletionItemProvider(
            TLAPLUS_CFG_FILE_SELECTOR,
            new CfgCompletionItemProvider()),
        vscode.languages.registerDeclarationProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaDeclarationsProvider(tlaDocInfos)
        ),
        vscode.languages.registerDefinitionProvider(
            TLAPLUS_FILE_SELECTOR,
            new TlaDefinitionsProvider(tlaDocInfos)
        )
    );
    syncTlcStatisticsSetting()
        .catch((err) => console.error(err))
        .then(() => listenTlcStatConfigurationChanges(context.subscriptions));
    showChangeLog(context.extensionPath)
        .catch((err) => console.error(err));
}

async function showChangeLog(extPath: string) {
    const pkgData = await readFile(`${extPath}${path.sep}package.json`);
    const curVersion = JSON.parse(pkgData).version;
    const prevFilePath = `${extPath}${path.sep}version`;
    let prevVersion;
    if (await exists(prevFilePath)) {
        prevVersion = await readFile(prevFilePath);
    }
    if (getMajorMinor(curVersion) === getMajorMinor(prevVersion)) {
        return;
    }
    await writeFile(prevFilePath, curVersion);
    const showOpt = 'Show changelog';
    const dismissOpt = 'Dismiss';
    const opt = await vscode.window.showInformationMessage('TLA+ extension has been updated.', showOpt, dismissOpt);
    if (opt === showOpt) {
        vscode.commands.executeCommand('vscode.open', CHANGELOG_URL);
    }
}

function getMajorMinor(version: string | undefined): string | undefined {
    if (!version || version === '') {
        return undefined;
    }
    const matches = /^(\d+.\d+)/g.exec(version);
    return matches ? matches[1] : undefined;
}

export function deactivate() {}
