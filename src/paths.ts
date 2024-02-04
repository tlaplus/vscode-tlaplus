import * as vscode from 'vscode';
import * as tla2tools from './tla2tools';

export const TLAPS = 'TLAPS';
export const TLC = 'TLC';
export const CFG = 'CFG';

export interface ModuleSearchPathSource {
    name: string;
    description: string;
}

class ModuleSearchPaths {
    private priority = [CFG, TLC, TLAPS];
    private sources: { [source: string]: string } = {};
    private paths: { [source: string]: string[] } = {};

    private _updates = new vscode.EventEmitter<void>();
    readonly updates = this._updates.event;

    public setup(context: vscode.ExtensionContext) {
        this.setSourcePaths(TLC, 'TLC Model Checker', tla2tools.moduleSearchPaths());
        const fromCfg = () => {
            const config = vscode.workspace.getConfiguration();
            const cfgPaths = config.get<string[]>('tlaplus.moduleSearchPaths');
            this.setSourcePaths(CFG, 'Configured Paths', cfgPaths ? cfgPaths : []);
        };
        context.subscriptions.push(vscode.workspace.onDidChangeConfiguration((e: vscode.ConfigurationChangeEvent) => {
            if (e.affectsConfiguration('tlaplus.moduleSearchPaths')) {
                fromCfg();
                vscode.commands.executeCommand(
                    'tlaplus.tlaps.moduleSearchPaths.updated.lsp',
                    ...this.getOtherPaths(TLAPS)
                );
            }
        }));
        fromCfg();
    }

    // Order first by the defined priority, then all the remaining alphabetically, just to be predictable.
    private sourceOrder(): string[] {
        const sourceNames = Object.keys(this.sources);
        const ordered: string[] = [];
        this.priority.forEach(sn => {
            if (sourceNames.includes(sn)) {
                ordered.push(sn);
            }
        });
        const other = sourceNames.filter(sn => !this.priority.includes(sn));
        other.sort();
        ordered.push(...other);
        return ordered;
    }

    public getSources(): ModuleSearchPathSource[] {
        return this.sourceOrder().map<ModuleSearchPathSource>(sn => {
            return {
                name: sn,
                description: this.sources[sn]
            };
        });
    }

    public getSourcePaths(source: string): string[] {
        return this.paths[source];
    }

    // Return all the paths except the specified source.
    public getOtherPaths(source: string): string[] {
        return this.sourceOrder().reduce<string[]>((acc, s) => {
            if (s !== source) {
                acc.push(... this.paths[s]);
            }
            return acc;
        }, []);
    }

    public setSourcePaths(source: string, description: string, paths: string[]) {
        this.sources[source] = description;
        this.paths[source] = paths;
        this._updates.fire();
    }
}

export const moduleSearchPaths = new ModuleSearchPaths();
