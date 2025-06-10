import * as vscode from 'vscode';
import * as path from 'path';
import { TlaMegaModuleGenerator } from './generators/megaModuleGenerator';
import { moduleSearchPaths } from './paths';
import { ModuleSymbolProvider } from './symbols/moduleSymbolProvider';

/**
 * Manages TLA+ module discovery and mega-module generation.
 */
export class ModuleDiscoveryManager {
    private generator: TlaMegaModuleGenerator | undefined;
    private symbolProvider: ModuleSymbolProvider;
    private isGenerating = false;
    private statusItem: vscode.StatusBarItem | undefined;

    constructor(private readonly context: vscode.ExtensionContext) {
        this.symbolProvider = new ModuleSymbolProvider();
    }

    /**
     * Initializes the module discovery system.
     */
    async initialize(): Promise<void> {
        // Check if module discovery is enabled
        const isEnabled = vscode.workspace.getConfiguration().get<boolean>('tlaplus.moduleDiscovery.enabled', true);
        if (!isEnabled) {
            return;
        }

        try {
            // Get paths to JAR files
            const toolsJarPath = path.resolve(this.context.extensionPath, 'tools/tla2tools.jar');
            const communityJarPath = path.resolve(this.context.extensionPath, 'tools/CommunityModules-deps.jar');

            // Create generator
            this.generator = new TlaMegaModuleGenerator(
                toolsJarPath,
                communityJarPath,
                vscode.workspace.workspaceFolders?.[0]
            );

            // Generate mega-modules if needed
            await this.regenerateIfNeeded();

            // Add mega-module paths to module search paths
            const cachePath = this.generator.getCachePath();
            moduleSearchPaths.setSourcePaths('MEGA_MODULES', 'Module Discovery Cache', [cachePath]);

            // Update symbol provider with mega-module paths
            const megaModulePaths = [
                path.join(cachePath, '_ALL_STANDARD.tla'),
                path.join(cachePath, '_ALL_CM.tla')
            ];
            this.symbolProvider.setMegaModulePaths(megaModulePaths);

            // Watch for JAR file changes
            this.setupFileWatchers(toolsJarPath, communityJarPath);

        } catch (error) {
            console.error('Failed to initialize module discovery:', error);
            vscode.window.showWarningMessage(`TLA+ module discovery initialization failed: ${error}`);
        }
    }

    /**
     * Regenerates mega-modules if they are stale.
     */
    private async regenerateIfNeeded(): Promise<void> {
        if (!this.generator || this.isGenerating) {
            return;
        }

        try {
            this.isGenerating = true;
            this.updateStatusBar('$(sync~spin) Indexing TLA+ modules...');

            const wasStale = await this.generator.isStale();
            if (wasStale) {
                console.log('Regenerating TLA+ mega-modules...');
                await this.generator.forceRegenerate();
                console.log('TLA+ mega-modules regenerated successfully');
            }

            this.updateStatusBar();
        } catch (error) {
            console.error('Failed to regenerate mega-modules:', error);
            this.updateStatusBar('$(error) Module indexing failed');
        } finally {
            this.isGenerating = false;
        }
    }

    /**
     * Sets up file watchers for JAR files.
     */
    private setupFileWatchers(toolsJarPath: string, communityJarPath: string): void {
        // Watch for changes to JAR files
        const jarWatcher = vscode.workspace.createFileSystemWatcher(
            new vscode.RelativePattern(path.dirname(toolsJarPath), '*.jar')
        );

        jarWatcher.onDidChange(async (uri) => {
            if (uri.fsPath === toolsJarPath || uri.fsPath === communityJarPath) {
                console.log(`JAR file changed: ${uri.fsPath}`);
                await this.regenerateIfNeeded();
            }
        });

        this.context.subscriptions.push(jarWatcher);
    }

    /**
     * Updates the status bar with module discovery status.
     */
    private updateStatusBar(text?: string): void {
        if (!this.statusItem) {
            this.statusItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
            this.context.subscriptions.push(this.statusItem);
        }

        if (text) {
            this.statusItem.text = text;
            this.statusItem.show();
        } else {
            this.statusItem.hide();
        }
    }

    /**
     * Gets the module symbol provider.
     */
    getSymbolProvider(): ModuleSymbolProvider {
        return this.symbolProvider;
    }

    /**
     * Registers module discovery commands.
     */
    registerCommands(): void {
        this.context.subscriptions.push(
            vscode.commands.registerCommand('tlaplus.refreshModuleIndex', async () => {
                if (!this.generator) {
                    vscode.window.showWarningMessage('Module discovery is not initialized');
                    return;
                }

                try {
                    this.isGenerating = true;
                    this.updateStatusBar('$(sync~spin) Refreshing module index...');
                    await this.generator.forceRegenerate();
                    vscode.window.showInformationMessage('TLA+ module index refreshed successfully');
                } catch (error) {
                    vscode.window.showErrorMessage(`Failed to refresh module index: ${error}`);
                } finally {
                    this.isGenerating = false;
                    this.updateStatusBar();
                }
            }),

            vscode.commands.registerCommand('tlaplus.showAvailableModules', async () => {
                if (!this.generator) {
                    vscode.window.showWarningMessage('Module discovery is not initialized');
                    return;
                }

                // TODO: Implement module list display
                vscode.window.showInformationMessage('Module list display not yet implemented');
            }),

            vscode.commands.registerCommand('tlaplus.clearModuleCache', async () => {
                if (!this.generator) {
                    vscode.window.showWarningMessage('Module discovery is not initialized');
                    return;
                }

                try {
                    await this.generator.clearCache();
                    vscode.window.showInformationMessage('Module cache cleared successfully');
                } catch (error) {
                    vscode.window.showErrorMessage(`Failed to clear module cache: ${error}`);
                }
            })
        );
    }
}