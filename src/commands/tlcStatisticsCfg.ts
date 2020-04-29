import * as vscode from 'vscode';
import * as path from 'path';
import { homedir } from 'os';
import { exists, readFile, writeFile, mkDir } from '../common';

export const CFG_TLC_STATISTICS_TYPE = 'tlaplus.tlc.statisticsSharing';
const STAT_SETTINGS_DIR = '.tlaplus';
const STAT_SETTINGS_FILE = 'esc.txt';
const STAT_OPT_SHARE_NO_ID = 'RANDOM_IDENTIFIER';
const STAT_OPT_DO_NOT_SHARE = 'NO_STATISTICS';

export enum ShareOption {
    Share = 'share',
    ShareWithoutId = 'shareWithoutId',
    DoNotShare = 'doNotShare'
}

/**
 * Writes TLC statistics sharing cfg file when the corresponding configuration setting is changed.
 */
export function listenTlcStatConfigurationChanges(disposables: vscode.Disposable[]) {
    vscode.workspace.onDidChangeConfiguration((event) => {
        if (event.affectsConfiguration(CFG_TLC_STATISTICS_TYPE)) {
            const cfgOption = vscode.workspace.getConfiguration().get<ShareOption>(CFG_TLC_STATISTICS_TYPE);
            if (cfgOption) {
                writeFileOption(cfgOption);
            }
        }
    }, undefined, disposables);
}

/**
 * Updates the TLC statistics sharing setting in accordance with the config file if necessary.
 */
export async function syncTlcStatisticsSetting() {
    const cfgOption = vscode.workspace.getConfiguration().get<string>(CFG_TLC_STATISTICS_TYPE);
    const fileOption = await readFileOption();
    if (cfgOption === fileOption) {
        return;
    }
    const target = vscode.ConfigurationTarget.Global;
    return vscode.workspace.getConfiguration().update(CFG_TLC_STATISTICS_TYPE, fileOption, target);
}

async function readFileOption(): Promise<ShareOption> {
    const file = path.join(homedir(), STAT_SETTINGS_DIR, STAT_SETTINGS_FILE);
    if (!await exists(file)) {
        return ShareOption.DoNotShare;
    }
    const fileContents = await readFile(file);
    if (fileContents.startsWith(STAT_OPT_DO_NOT_SHARE)) {
        return ShareOption.DoNotShare;
    } else if (fileContents.startsWith(STAT_OPT_SHARE_NO_ID)) {
        return ShareOption.ShareWithoutId;
    } else if (fileContents.length > 0) {
        return ShareOption.Share;
    }
    return ShareOption.DoNotShare;
}

async function writeFileOption(option: ShareOption) {
    let contents;
    switch (option) {
        case ShareOption.Share:
            contents = generateRandomInstallationId();
            break;
        case ShareOption.ShareWithoutId:
            contents = STAT_OPT_SHARE_NO_ID;
            break;
        case ShareOption.DoNotShare:
            contents = STAT_OPT_DO_NOT_SHARE;
            break;
        default:
            console.error('Unsupported TLC statistics option: ' + option);
            return;
    }
    const dir = path.join(homedir(), STAT_SETTINGS_DIR);
    const file = path.join(dir, STAT_SETTINGS_FILE);
    if (!await exists(dir)) {
        await mkDir(dir);
    }
    return writeFile(file, contents + '\n');
}

function generateRandomInstallationId(): string {
    const id = [];
    for (let i = 0; i < 32; i++) {
        const n = i % 2;
        id.push((n ^ Math.random() * 16 >> n / 4).toString(16));
    }
    return id.join('');
}
