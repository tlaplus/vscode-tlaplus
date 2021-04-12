import * as vscode from 'vscode';
import * as path from 'path';
import * as cp from 'child_process';
import * as fs from 'fs';
import { ChildProcess, spawn } from 'child_process';
import { pathToUri } from './common';
import { JavaVersionParser } from './parsers/javaVersion';
import { ShareOption, CFG_TLC_STATISTICS_TYPE } from './commands/tlcStatisticsCfg';
import { ToolOutputChannel } from './outputChannels';

const CFG_JAVA_HOME = 'tlaplus.java.home';
const CFG_JAVA_OPTIONS = 'tlaplus.java.options';
const CFG_TLC_OPTIONS = 'tlaplus.tlc.modelChecker.options';
const CFG_PLUSCAL_OPTIONS = 'tlaplus.pluscal.options';

const VAR_TLC_SPEC_NAME = /\$\{specName\}/g;
const VAR_TLC_MODEL_NAME = /\$\{modelName\}/g;

const NO_ERROR = 0;
const MIN_TLA_ERROR = 10;           // Exit codes not related to tooling start from this number
const LOWEST_JAVA_VERSION = 8;
const DEFAULT_GC_OPTION = '-XX:+UseParallelGC';
const TLA_TOOLS_LIB_NAME = 'tla2tools.jar';
const TLA_TOOLS_LIB_NAME_END_UNIX = '/' + TLA_TOOLS_LIB_NAME;
const TLA_TOOLS_LIB_NAME_END_WIN = '\\' + TLA_TOOLS_LIB_NAME;
const toolsJarPath = path.resolve(__dirname, '../../tools/' + TLA_TOOLS_LIB_NAME);
const javaCmd = 'java' + (process.platform === 'win32' ? '.exe' : '');
const javaVersionChannel = new ToolOutputChannel('TLA+ Java version');

let lastUsedJavaHome: string | undefined;
let cachedJavaPath: string | undefined;

enum TlaTool {
    PLUS_CAL = 'pcal.trans',
    SANY = 'tla2sany.SANY',
    TLC = 'tlc2.TLC',
    TEX = 'tla2tex.TLA'
}

export class ToolProcessInfo {
    constructor(
        readonly commandLine: string,
        readonly process: ChildProcess
    ) {}
}

/**
 * Thrown when there's some problem with Java or TLA+ tooling.
 */
export class ToolingError extends Error {
    constructor(message: string) {
        super(message);
    }
}

export class JavaVersion {
    static UNKNOWN_VERSION = '?';

    constructor(
        readonly version: string,
        readonly fullOutput: string[]
    ) {}
}

export async function runPlusCal(tlaFilePath: string): Promise<ToolProcessInfo> {
    const customOptions = getConfigOptions(CFG_PLUSCAL_OPTIONS);
    return runTool(
        TlaTool.PLUS_CAL,
        tlaFilePath,
        buildPlusCalOptions(tlaFilePath, customOptions),
        []
    );
}

export async function runSany(tlaFilePath: string): Promise<ToolProcessInfo> {
    return runTool(
        TlaTool.SANY,
        tlaFilePath,
        [ path.basename(tlaFilePath) ],
        []
    );
}

export async function runTex(tlaFilePath: string): Promise<ToolProcessInfo> {
    return runTool(
        TlaTool.TEX,
        tlaFilePath,
        [ path.basename(tlaFilePath) ],
        []
    );
}

export async function runTlc(tlaFilePath: string, cfgFilePath: string): Promise<ToolProcessInfo | undefined> {
    const customOptions = await getTlcOptions();
    if (customOptions === undefined) {
        // Command cancelled by user
        return undefined;
    }
    const javaOptions = [];
    const shareStats = vscode.workspace.getConfiguration().get<ShareOption>(CFG_TLC_STATISTICS_TYPE);
    if (shareStats !== ShareOption.DoNotShare) {
        javaOptions.push('-Dtlc2.TLC.ide=vscode');
    }
    return runTool(
        TlaTool.TLC,
        tlaFilePath,
        buildTlcOptions(tlaFilePath, cfgFilePath, customOptions),
        javaOptions
    );
}

async function runTool(
    toolName: string,
    filePath: string,
    toolOptions: string[],
    javaOptions: string[]
): Promise<ToolProcessInfo> {
    const javaPath = await obtainJavaPath();
    const cfgOptions = getConfigOptions(CFG_JAVA_OPTIONS);
    const args = buildJavaOptions(cfgOptions, toolsJarPath).concat(javaOptions);
    args.push(toolName);
    toolOptions.forEach(opt => args.push(opt));
    const proc = spawn(javaPath, args, { cwd: path.dirname(filePath) });
    addReturnCodeHandler(proc, toolName);
    return new ToolProcessInfo(buildCommandLine(javaPath, args), proc);
}

/**
 * Kills the given process.
 */
export function stopProcess(p: cp.ChildProcess): void {
    if (!p.killed) {
        p.kill('SIGINT');
    }
}

async function obtainJavaPath(): Promise<string> {
    const javaHome = vscode.workspace.getConfiguration().get<string>(CFG_JAVA_HOME);
    if (cachedJavaPath && javaHome === lastUsedJavaHome) {
        return cachedJavaPath;
    }
    const javaPath = buildJavaPath();
    cachedJavaPath = javaPath;
    lastUsedJavaHome = javaHome;
    await checkJavaVersion(javaPath);
    return javaPath;
}

/**
 * Builds path to the Java executable based on the configuration.
 */
function buildJavaPath(): string {
    let javaPath = javaCmd;
    const javaHome = vscode.workspace.getConfiguration().get<string>(CFG_JAVA_HOME);
    if (javaHome) {
        const homeUri = pathToUri(javaHome);
        javaPath = homeUri.fsPath + path.sep + 'bin' + path.sep + javaCmd;
        if (!fs.existsSync(javaPath)) {
            throw new ToolingError('Java executable not found. Check the Java Home setting.');
        }
    }
    return javaPath;
}

/**
 * Builds an array of options to pass to Java process when running TLA tools.
 */
export function buildJavaOptions(customOptions: string[], defaultClassPath: string): string[] {
    const opts = customOptions.slice(0);
    mergeClassPathOption(opts, defaultClassPath);
    mergeGCOption(opts, DEFAULT_GC_OPTION);
    return opts;
}

/**
 * Builds an array of options to pass to the TLC tool.
 */
export function buildTlcOptions(tlaFilePath: string, cfgFilePath: string, customOptions: string[]): string[] {
    const custOpts = customOptions.map((opt) => {
        return opt
            .replace(VAR_TLC_SPEC_NAME, path.basename(tlaFilePath, '.tla'))
            .replace(VAR_TLC_MODEL_NAME, path.basename(cfgFilePath, '.cfg'));
    });
    const opts = [path.basename(tlaFilePath), '-tool', '-modelcheck'];
    addValueOrDefault('-config', cfgFilePath, custOpts, opts);
    return opts.concat(custOpts);
}

/**
 * Builds an array of options to pass to the PlusCal tool.
 */
export function buildPlusCalOptions(tlaFilePath: string, customOptions: string[]): string[] {
    const opts = customOptions.slice(0);
    opts.push(path.basename(tlaFilePath));
    return opts;
}

/**
 * Splits the given string into an array of command line arguments.
 */
export function splitArguments(str: string): string[] {
    const regEx = /(?:[^\s'"]+|"(?:\\.|[^"]|\s)*"|'(?:\\.|[^']|\s)*')/g;
    const matches = str.match(regEx);
    if (!matches) {
        return [];
    }
    return matches
        .map(opt => opt.trim())
        .filter(opt => opt !== '')
        .map(opt => removeQuotes(opt));         // This must not be put before throwing out empty strings
}

/**
 * Executes java -version and analyzes, if the version is 1.8 or higher.
 */
async function checkJavaVersion(javaPath: string) {
    const proc = spawn(javaPath, ['-version']);
    const parser = new JavaVersionParser(proc.stderr);
    const ver = await parser.readAll();
    if (ver.version === JavaVersion.UNKNOWN_VERSION) {
        ver.fullOutput.forEach(line => console.debug(line));
        throw new ToolingError('Error while obtaining Java version. Check the Java Home setting.');
    }
    const majVersion = extractMajor(ver.version);
    if (majVersion >= LOWEST_JAVA_VERSION) {
        return;
    }
    vscode.window.showWarningMessage(
        `Unsupported Java version: ${ver.version}`,
        'Show Details'
    ).then(() => showJavaVersionOutput(javaPath, ver));
}

function addValueOrDefault(option: string, defaultValue: string, args: string[], realArgs: string[]) {
    realArgs.push(option);
    const idx = args.indexOf(option);
    if (idx < 0 || idx === args.length - 1) {
        realArgs.push(defaultValue);
    } else {
        realArgs.push(args[idx + 1]);
        args.splice(idx, 2);
    }
}

/**
 * Adds a handler to the given TLA+ tooling process that captures various system errors.
 */
function addReturnCodeHandler(proc: ChildProcess, toolName?: string) {
    const stderr: string[] = [];
    proc.stderr?.on('data', chunk => {
        stderr.push(String(chunk));
    });
    proc.on('close', exitCode => {
        if (exitCode !== NO_ERROR && exitCode < MIN_TLA_ERROR) {
            const details = stderr.join('\n');
            vscode.window.showErrorMessage(`Error running ${toolName} (exit code ${exitCode})\n${details}`);
        }
    });
}

function getConfigOptions(cfgName: string): string[] {
    const optsString = vscode.workspace.getConfiguration().get<string>(cfgName) || '';
    return splitArguments(optsString);
}

export async function getTlcOptions(): Promise<string[] | undefined> {
    const defaultOptions = '-coverage 1';
    // -config is not shown as an option by default so the same options can be used without modification across
    // multiple modules.
    const customOptions = await vscode.window.showInputBox({
        value: vscode.workspace.getConfiguration().get<string>(CFG_TLC_OPTIONS) || defaultOptions,
        prompt: 'Additional options to pass to TLC.',
        // Ignoring focus changes allows users to click out to a different window to check potential TLC options
        // without getting rid of what they've typed so far.
        ignoreFocusOut: true,
    });
    if (customOptions === undefined) {
        // Command cancelled by user
        return undefined;
    } else {
        // Save user-enterred options as new configuration to persist between sessions. If a workspace is open, the
        // configuration is saved at the workspace level. Otherwise it is saved at the global level.
        const workspaceOpen = vscode.workspace.name !== undefined;
        const configurationTarget = workspaceOpen ?
            vscode.ConfigurationTarget.Workspace :
            vscode.ConfigurationTarget.Global;
        vscode.workspace.getConfiguration().update(CFG_TLC_OPTIONS, customOptions, configurationTarget);
    }
    return splitArguments(customOptions);
}

function buildCommandLine(programName: string, args: string[]): string {
    const line = [ programName ];
    args
        .map(arg => arg.indexOf(' ') >= 0 ? '"' + arg + '"' : arg)
        .forEach(arg => line.push(arg));
    return line.join(' ');
}

/**
 * Adds the default GC option if no custom one is provided.
 */
function mergeGCOption(options: string[], defaultGC: string) {
    const gcOption = options.find(opt => opt.startsWith('-XX:+Use') && opt.endsWith('GC'));
    if (!gcOption) {
        options.push(defaultGC);
    }
}

/**
 * Searches for -cp or -classpath option and merges its value with the default classpath.
 * Custom libraries must be given precedence over default ones.
 */
function mergeClassPathOption(options: string[], defaultClassPath: string) {
    let cpIdx = -1;
    for (let i = 0; i < options.length; i++) {
        const option = options[i];
        if (option === '-cp' || option === '-classpath') {
            cpIdx = i + 1;
            break;
        }
    }
    if (cpIdx < 0 || cpIdx >= options.length) {
        // No custom classpath provided, use the default one
        options.push('-cp', defaultClassPath);
        return;
    }
    let classPath = options[cpIdx];
    if (containsTlaToolsLib(classPath)) {
        return;
    }
    if (classPath.length > 0) {
        classPath += path.delimiter;
    }
    classPath += defaultClassPath;
    options[cpIdx] = classPath;
}

function containsTlaToolsLib(classPath: string): boolean {
    const paths = classPath.split(path.delimiter);
    for (const p of paths) {
        if (p === TLA_TOOLS_LIB_NAME
            || p.endsWith(TLA_TOOLS_LIB_NAME_END_UNIX)
            || p.endsWith(TLA_TOOLS_LIB_NAME_END_WIN)
        ) {
            return true;
        }
    }
    return false;
}

/**
 * Extracts the "major" Java version: 1.6.80 => 6, 1.8.202 => 8, 9.0.7 => 9, 11.0.6 => 11 etc.
 * @param version The full version as reported by `java -version`.
 */
function extractMajor(version: string): number {
    let majVer = version;
    if (majVer.startsWith('1.')) {
        majVer = majVer.substring(2);
    }
    const pIdx = majVer.indexOf('.');
    if (pIdx > 0) {
        majVer = majVer.substring(0, pIdx);
    }
    return parseInt(majVer, 10);
}

/**
 * Shows full Java version output in an Output channel.
 */
function showJavaVersionOutput(javaPath: string, ver: JavaVersion) {
    javaVersionChannel.clear();
    javaVersionChannel.appendLine(`${javaPath} -version`);
    ver.fullOutput.forEach(line => javaVersionChannel.appendLine(line));
    javaVersionChannel.revealWindow();
}

/**
 * Trims quotes from the given string.
 */
function removeQuotes(str: string): string {
    return str.length > 1 && (isQuoted(str, '"') || isQuoted(str, "'"))
        ? str.substring(1, str.length - 1)
        : str;
}

function isQuoted(str: string, q: string): boolean {
    return str.startsWith(q) && str.endsWith(q);
}
