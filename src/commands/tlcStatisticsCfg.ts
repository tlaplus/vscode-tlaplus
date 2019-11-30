import * as vscode from 'vscode';
import * as path from 'path';
import { homedir } from 'os';
import { exists, readFile, writeFile, mkDir } from '../common';

const CFG_TLC_STATISTICS_TYPE = 'tlaplus.tlc.statisticsSharing';
const STAT_SETTINGS_DIR = '.tlaplus';
const STAT_SETTINGS_FILE = 'esc.txt';
const STAT_OPT_SHARE = '*';
const STAT_OPT_SHARE_NO_ID = 'RANDOM_IDENTIFIER';
const STAT_OPT_DO_NOT_SHARE = 'NO_STATISTICS';

let lastStatCfgValue: string | undefined;

/**
 * Checks the TLC statistics collection setting, rewrites the statistics config file if necessary.
 * The statistics config file contains one of the following:
 * - {installation ID} - when the user allows to share statistics along with the installation ID.
 * - NO_STATISTICS - when the user doesn't want to share statistics.
 * - RANDOM_IDENTIFIER - when the user allows to share statistics but without the installation ID.
 * TLC handles this file automatically when running.
 */
export async function processTlcStatisticsSetting() {
    const statCfg = vscode.workspace.getConfiguration().get<string>(CFG_TLC_STATISTICS_TYPE);
    if (statCfg === lastStatCfgValue) {
        return;
    }
    lastStatCfgValue = statCfg;
    switch (statCfg) {
        case 'share':
            setStatisticsSetting(STAT_OPT_SHARE);
            break;
        case 'shareWithoutId':
            setStatisticsSetting(STAT_OPT_SHARE_NO_ID);
            break;
        case 'doNotShare':
            setStatisticsSetting(STAT_OPT_DO_NOT_SHARE);
            break;
        default:
            console.error('Unsupported TLC statistics option: ' + statCfg);
            return;
    }
}

async function setStatisticsSetting(option: string) {
    const dir = path.join(homedir(), STAT_SETTINGS_DIR);
    const file = path.join(dir, STAT_SETTINGS_FILE);
    if (await exists(file)) {
        const curOption = await readFile(file);
        if ((option === STAT_OPT_DO_NOT_SHARE || option === STAT_OPT_SHARE_NO_ID) && curOption.startsWith(option)) {
            return;
        }
        if (option === STAT_OPT_SHARE
                && !curOption.startsWith(STAT_OPT_DO_NOT_SHARE)
                && !curOption.startsWith(STAT_OPT_SHARE_NO_ID)) {
            return;
        }
    }
    const fileContents = option === STAT_OPT_SHARE ? generateRandomInstallationId() : option;
    if (!await exists(dir)) {
        await mkDir(dir);
    }
    await writeFile(file, fileContents + '\n');
}

function generateRandomInstallationId(): string {
    const id = [];
    for (let i = 0; i < 32; i++) {
        const n = i % 2;
        id.push((n ^ Math.random() * 16 >> n / 4).toString(16));
    }
    return id.join('');
}
