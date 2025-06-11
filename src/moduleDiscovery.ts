import * as vscode from 'vscode';
import * as path from 'path';
import { TlaMegaModuleGenerator } from './generators/megaModuleGenerator';
import { moduleSearchPaths } from './paths';
import { ModuleSymbolProvider } from './symbols/moduleSymbolProvider';
import { ModuleExplorer } from './ui/moduleExplorer';
import { JarModuleReader } from './utils/jarReader';
import { ModuleDocumentProvider } from './providers/moduleDocumentProvider';
import { ModuleExplorerTreeProvider, ModuleExplorerPanel } from './panels/moduleExplorerTreeProvider';

/**
 * Manages TLA+ module discovery and mega-module generation.
 */
export class ModuleDiscoveryManager {
    private generator: TlaMegaModuleGenerator | undefined;
    private symbolProvider: ModuleSymbolProvider;
    private moduleExplorer: ModuleExplorer | undefined;
    private jarReader: JarModuleReader;
    private documentProvider: ModuleDocumentProvider | undefined;
    private moduleExplorerPanel: ModuleExplorerPanel | undefined;
    private isGenerating = false;
    private statusItem: vscode.StatusBarItem | undefined;

    constructor(private readonly context: vscode.ExtensionContext) {
        this.symbolProvider = new ModuleSymbolProvider();
        this.jarReader = new JarModuleReader();
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

            // Create module explorer
            this.moduleExplorer = new ModuleExplorer(
                this.jarReader,
                this.symbolProvider,
                toolsJarPath,
                communityJarPath
            );

            // Create and register document provider
            this.documentProvider = new ModuleDocumentProvider(
                this.jarReader,
                toolsJarPath,
                communityJarPath
            );

            const providerRegistration = vscode.workspace.registerTextDocumentContentProvider(
                'tla-module',
                this.documentProvider
            );
            this.context.subscriptions.push(providerRegistration);

            // Create Module Explorer tree view
            const treeDataProvider = new ModuleExplorerTreeProvider(
                this.jarReader,
                this.symbolProvider,
                toolsJarPath,
                communityJarPath
            );
            this.moduleExplorerPanel = new ModuleExplorerPanel(
                this.context,
                treeDataProvider
            );

            // Generate mega-modules if needed
            const wasStale = await this.generator.isStale();
            await this.regenerateIfNeeded();

            // Add mega-module paths to module search paths
            const cachePath = this.generator.getCachePath();
            moduleSearchPaths.setSourcePaths('MEGA_MODULES', 'Module Discovery Cache', [cachePath]);

            // Update symbol provider with mega-module paths
            const megaModulePaths = [
                path.join(cachePath, '_ALL_STANDARD.tla'),
                path.join(cachePath, '_ALL_CM.tla')
            ];
            await this.symbolProvider.setMegaModulePaths(megaModulePaths, cachePath);

            // Watch for JAR file changes
            this.setupFileWatchers(toolsJarPath, communityJarPath);

            // Show welcome message if this was the first time
            if (wasStale) {
                const message = 'TLA+ module discovery is ready! ' +
                    'Use the Module Explorer or type module names to see available operators.';
                vscode.window.showInformationMessage(message, 'Show Modules'
                ).then(selection => {
                    if (selection === 'Show Modules') {
                        vscode.commands.executeCommand('tlaplus.showAvailableModules');
                    }
                });
            }

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

                // Show progress notification
                await vscode.window.withProgress({
                    location: vscode.ProgressLocation.Notification,
                    title: 'TLA+ Module Discovery',
                    cancellable: false
                }, async (progress) => {
                    progress.report({ increment: 0, message: 'Checking module cache...' });

                    progress.report({ increment: 30, message: 'Generating standard modules index...' });
                    if (this.generator) {
                        await this.generator.generateStandardModules();
                    }

                    progress.report({ increment: 60, message: 'Generating community modules index...' });
                    if (this.generator) {
                        await this.generator.generateCommunityModules();
                    }

                    progress.report({ increment: 90, message: 'Parsing module symbols...' });
                    await this.symbolProvider.clearCache();

                    progress.report({ increment: 100, message: 'Module index ready!' });
                });

                console.log('TLA+ mega-modules regenerated successfully');
            }

            this.updateStatusBar();
        } catch (error) {
            console.error('Failed to regenerate mega-modules:', error);
            this.updateStatusBar('$(error) Module indexing failed');
            vscode.window.showErrorMessage(`Module indexing failed: ${error}`);
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

                    await vscode.window.withProgress({
                        location: vscode.ProgressLocation.Notification,
                        title: 'Refreshing TLA+ Module Index',
                        cancellable: false
                    }, async (progress) => {
                        progress.report({ increment: 0, message: 'Clearing cache...' });
                        if (this.generator) {
                            await this.generator.clearCache();
                        }
                        this.jarReader.clearCache();
                        this.symbolProvider.clearCache();

                        progress.report({ increment: 20, message: 'Scanning standard modules...' });
                        if (this.generator) {
                            await this.generator.generateStandardModules();
                        }

                        progress.report({ increment: 50, message: 'Scanning community modules...' });
                        if (this.generator) {
                            await this.generator.generateCommunityModules();
                        }

                        progress.report({ increment: 80, message: 'Parsing module symbols...' });
                        // Force symbol reload by clearing paths and resetting
                        const cachePath = this.generator ? this.generator.getCachePath() : '';
                        await this.symbolProvider.setMegaModulePaths([], cachePath);
                        const megaModulePaths = [
                            path.join(cachePath, '_ALL_STANDARD.tla'),
                            path.join(cachePath, '_ALL_CM.tla')
                        ];
                        await this.symbolProvider.setMegaModulePaths(megaModulePaths, cachePath);

                        progress.report({ increment: 100, message: 'Module index updated!' });
                    });

                    vscode.window.showInformationMessage('TLA+ module index refreshed successfully');
                } catch (error) {
                    vscode.window.showErrorMessage(`Failed to refresh module index: ${error}`);
                } finally {
                    this.isGenerating = false;
                    this.updateStatusBar();
                }
            }),

            vscode.commands.registerCommand('tlaplus.showAvailableModules', async () => {
                if (!this.moduleExplorer) {
                    vscode.window.showWarningMessage('Module discovery is not initialized');
                    return;
                }

                await this.moduleExplorer.showModuleExplorer();
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