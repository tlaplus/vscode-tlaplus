import { copyFile } from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { exists, listFiles, replaceExtension } from '../common';

const TEMPLATE_CFG_PATH = path.resolve(__dirname, '../tools/template.cfg');

export type ModelResolveMode = 'adjacent' | 'customPick';

export interface ResolvedModel {
    tlaPath: string;
    cfgPath: string;
    modelName: string;
    outputDir: string;
    source: 'explicit' | 'adjacent';
}

interface CandidateModel {
    tlaPath: string;
    cfgPath: string;
    modelName: string;
    source: 'explicit' | 'adjacent';
}

function buildResolvedModel(candidate: CandidateModel): ResolvedModel {
    return {
        tlaPath: candidate.tlaPath,
        cfgPath: candidate.cfgPath,
        modelName: candidate.modelName,
        outputDir: path.dirname(candidate.cfgPath),
        source: candidate.source
    };
}

async function resolveFromCfg(
    cfgPath: string,
    warn: boolean,
    interactive: boolean
): Promise<ResolvedModel | undefined> {
    const tlaPath = replaceExtension(cfgPath, 'tla');
    if (!await exists(tlaPath)) {
        if (warn && interactive) {
            const moduleFile = path.basename(tlaPath);
            vscode.window.showWarningMessage(`Corresponding TLA+ module file ${moduleFile} doesn't exist.`);
        }
        return undefined;
    }
    const modelName = path.parse(cfgPath).name;
    return buildResolvedModel({
        tlaPath,
        cfgPath,
        modelName,
        source: 'explicit'
    });
}

async function resolveFromCustomPick(
    tlaPath: string,
    warn: boolean,
    interactive: boolean
): Promise<ResolvedModel | undefined> {
    if (!interactive) {
        return resolveFromTla(tlaPath, warn, interactive);
    }
    const dir = path.dirname(tlaPath);
    const files = await listFiles(dir, (fName) => fName.endsWith('.cfg') || fName.endsWith('.tla'));
    files.sort();
    const cfgFileName = await vscode.window.showQuickPick(
        files,
        { canPickMany: false, placeHolder: 'Select a model config file', matchOnDetail: true }
    );
    if (!cfgFileName || cfgFileName.length === 0) {
        return undefined;
    }
    const cfgPath = path.join(dir, cfgFileName);
    return buildResolvedModel({
        tlaPath,
        cfgPath,
        modelName: path.parse(cfgPath).name,
        source: 'explicit'
    });
}

async function resolveFromTla(
    tlaPath: string,
    warn: boolean,
    interactive: boolean
): Promise<ResolvedModel | undefined> {
    const dir = path.dirname(tlaPath);
    const baseName = path.basename(tlaPath, '.tla');

    const specCfgPath = path.join(dir, `${baseName}.cfg`);
    const mcBaseName = baseName.startsWith('MC') ? undefined : `MC${baseName}`;
    const mcTlaPath = mcBaseName ? path.join(dir, `${mcBaseName}.tla`) : undefined;
    const mcCfgPath = mcBaseName ? path.join(dir, `${mcBaseName}.cfg`) : undefined;

    const candidates: CandidateModel[] = [];
    if (await exists(specCfgPath)) {
        candidates.push({
            tlaPath,
            cfgPath: specCfgPath,
            modelName: baseName,
            source: 'adjacent'
        });
    }

    if (mcBaseName && mcCfgPath && mcTlaPath && await exists(mcCfgPath) && await exists(mcTlaPath)) {
        candidates.push({
            tlaPath: mcTlaPath,
            cfgPath: mcCfgPath,
            modelName: mcBaseName,
            source: 'adjacent'
        });
    }

    if (candidates.length === 0) {
        if (warn && interactive) {
            showConfigAbsenceWarning(specCfgPath);
        }
        return undefined;
    }

    if (candidates.length === 1 || !interactive) {
        if (!interactive) {
            const specCandidate = candidates.find(candidate => candidate.cfgPath === specCfgPath);
            if (specCandidate) {
                return buildResolvedModel(specCandidate);
            }
        }
        return buildResolvedModel(candidates[0]);
    }

    const pickItems = candidates.map(candidate => ({
        label: candidate.modelName,
        description: path.basename(candidate.cfgPath),
        detail: candidate.cfgPath,
        candidate
    }));

    const selected = await vscode.window.showQuickPick(pickItems, {
        canPickMany: false,
        placeHolder: 'Select a model config file',
        matchOnDetail: true
    });

    if (!selected) {
        return undefined;
    }

    return buildResolvedModel(selected.candidate);
}

export async function resolveModelForUri(
    fileUri: vscode.Uri,
    warn: boolean = true,
    interactive: boolean = true,
    mode: ModelResolveMode = 'adjacent'
): Promise<ResolvedModel | undefined> {
    const filePath = fileUri.fsPath;
    if (filePath.endsWith('.cfg')) {
        return resolveFromCfg(filePath, warn, interactive);
    }
    if (filePath.endsWith('.tla')) {
        if (mode === 'customPick') {
            return resolveFromCustomPick(filePath, warn, interactive);
        }
        return resolveFromTla(filePath, warn, interactive);
    }
    if (warn && interactive) {
        vscode.window.showWarningMessage('File in the active editor is not a .tla or .cfg file.');
    }
    return undefined;
}

function showConfigAbsenceWarning(cfgPath: string) {
    const fileName = path.basename(cfgPath);
    const createOption = 'Create model file';
    vscode.window.showWarningMessage(`Model file ${fileName} doesn't exist. Cannot check model.`, createOption)
        .then((option) => {
            if (option === createOption) {
                createModelFile(cfgPath);
            }
        });
}

function createModelFile(cfgPath: string) {
    copyFile(TEMPLATE_CFG_PATH, cfgPath, (err) => {
        if (err) {
            console.warn(`Error creating config file: ${err}`);
            vscode.window.showWarningMessage(`Cannot create model file: ${err}`);
            return;
        }
        vscode.workspace.openTextDocument(cfgPath)
            .then(doc => vscode.window.showTextDocument(doc));
    });
}
