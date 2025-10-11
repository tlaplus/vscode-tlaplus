import * as vscode from 'vscode';
import AdmZip from 'adm-zip';
import { existsSync } from 'fs';

/**
 * A FileSystemProvider that allows read-only access to files inside JAR/ZIP archives.
 *
 * URI format: jarfile:/path/to/archive.jar!/path/inside/archive
 *
 * This provider supports:
 * - Reading files from JAR/ZIP archives
 * - Listing directory contents within archives
 * - Getting file metadata (stat)
 *
 * This provider does NOT support:
 * - Writing files
 * - Creating directories
 * - Deleting files
 * - Renaming files
 * - File watching (since archive content is static)
 */
export class JarFileSystemProvider implements vscode.FileSystemProvider {
    private readonly _emitter = new vscode.EventEmitter<vscode.FileChangeEvent[]>();
    readonly onDidChangeFile: vscode.Event<vscode.FileChangeEvent[]> = this._emitter.event;

    /**
     * Cache for ZIP instances to avoid repeatedly opening the same archive
     */
    private readonly zipCache = new Map<string, AdmZip>();

    /**
     * Parse a jarfile: URI into archive path and internal path
     * @param uri URI in format jarfile:/path/to/archive.jar!/internal/path
     */
    private parseJarUri(uri: vscode.Uri): { archivePath: string; internalPath: string } {
        if (uri.scheme !== 'jarfile') {
            throw vscode.FileSystemError.FileNotFound(uri);
        }

        // URI format: jarfile:/path/to/archive.jar!/path/inside/archive
        // uri.path will be /path/to/archive.jar!/path/inside/archive
        const uriPath = uri.path;
        const separatorIndex = uriPath.indexOf('!/');

        if (separatorIndex === -1) {
            throw new Error(`Invalid jarfile URI format. Expected jarfile:/archive.jar!/path, got: ${uri.toString()}`);
        }

        const archivePath = uriPath.substring(0, separatorIndex);
        const internalPath = uriPath.substring(separatorIndex + 2); // Skip '!/'

        return { archivePath, internalPath };
    }

    /**
     * Get or create a ZIP instance for the given archive path
     */
    private getZipInstance(archivePath: string): AdmZip {
        if (!existsSync(archivePath)) {
            throw vscode.FileSystemError.FileNotFound(`Archive not found: ${archivePath}`);
        }

        let zip = this.zipCache.get(archivePath);
        if (!zip) {
            try {
                zip = new AdmZip(archivePath);
                this.zipCache.set(archivePath, zip);
            } catch (error) {
                throw vscode.FileSystemError.FileNotFound(`Failed to open archive: ${archivePath}`);
            }
        }
        return zip;
    }

    /**
     * Normalize internal path (remove leading slash, handle empty paths)
     */
    private normalizeInternalPath(internalPath: string): string {
        if (!internalPath || internalPath === '/') {
            return '';
        }
        return internalPath.startsWith('/') ? internalPath.substring(1) : internalPath;
    }

    // FileSystemProvider implementation

    watch(uri: vscode.Uri, options: { recursive: boolean; excludes: readonly string[] }): vscode.Disposable {
        // Archive content is static, so we don't need to watch for changes
        return new vscode.Disposable(() => {
            // No cleanup needed for archive watching
        });
    }

    stat(uri: vscode.Uri): vscode.FileStat | Thenable<vscode.FileStat> {
        const { archivePath, internalPath } = this.parseJarUri(uri);
        const zip = this.getZipInstance(archivePath);
        const normalizedPath = this.normalizeInternalPath(internalPath);

        // Check if it's the root directory
        if (normalizedPath === '') {
            return {
                type: vscode.FileType.Directory,
                ctime: 0,
                mtime: 0,
                size: 0
            };
        }

        // Look for exact file match
        const entry = zip.getEntry(normalizedPath);
        if (entry) {
            return {
                type: entry.isDirectory ? vscode.FileType.Directory : vscode.FileType.File,
                ctime: entry.header.time.getTime(),
                mtime: entry.header.time.getTime(),
                size: entry.header.size
            };
        }

        // Check if it's a directory by looking for entries that start with this path
        const pathWithSlash = normalizedPath.endsWith('/') ? normalizedPath : normalizedPath + '/';
        const entries = zip.getEntries();
        const hasChildEntries = entries.some(e => e.entryName.startsWith(pathWithSlash));

        if (hasChildEntries) {
            return {
                type: vscode.FileType.Directory,
                ctime: 0,
                mtime: 0,
                size: 0
            };
        }

        throw vscode.FileSystemError.FileNotFound(uri);
    }

    readDirectory(uri: vscode.Uri): [string, vscode.FileType][] | Thenable<[string, vscode.FileType][]> {
        const { archivePath, internalPath } = this.parseJarUri(uri);
        const zip = this.getZipInstance(archivePath);
        const normalizedPath = this.normalizeInternalPath(internalPath);

        const entries = zip.getEntries();
        const result: [string, vscode.FileType][] = [];
        const pathPrefix = normalizedPath === '' ? '' : normalizedPath + '/';
        const seenNames = new Set<string>();

        for (const entry of entries) {
            const entryName = entry.entryName;

            // Skip entries that don't start with our path prefix
            if (!entryName.startsWith(pathPrefix)) {
                continue;
            }

            // Get the relative path from our directory
            const relativePath = entryName.substring(pathPrefix.length);

            // Skip if this is the directory itself (empty relative path)
            if (relativePath === '') {
                continue;
            }

            // For subdirectories, we only want the immediate child name
            const slashIndex = relativePath.indexOf('/');
            const childName = slashIndex === -1 ? relativePath : relativePath.substring(0, slashIndex);

            // Skip if we've already seen this name
            if (seenNames.has(childName)) {
                continue;
            }
            seenNames.add(childName);

            // Determine if it's a file or directory
            const isDirectory = slashIndex !== -1 || entry.isDirectory;
            const fileType = isDirectory ? vscode.FileType.Directory : vscode.FileType.File;

            result.push([childName, fileType]);
        }

        return result;
    }

    readFile(uri: vscode.Uri): Uint8Array | Thenable<Uint8Array> {
        const { archivePath, internalPath } = this.parseJarUri(uri);
        const zip = this.getZipInstance(archivePath);
        const normalizedPath = this.normalizeInternalPath(internalPath);

        const entry = zip.getEntry(normalizedPath);
        if (!entry || entry.isDirectory) {
            throw vscode.FileSystemError.FileNotFound(uri);
        }

        try {
            const data = entry.getData();
            return new Uint8Array(data);
        } catch (error) {
            throw vscode.FileSystemError.FileNotFound(`Failed to read file from archive: ${error}`);
        }
    }

    // Write operations - not supported for read-only provider
    createDirectory(uri: vscode.Uri): void | Thenable<void> {
        throw vscode.FileSystemError.NoPermissions('JarFileSystemProvider is read-only');
    }

    writeFile(
        uri: vscode.Uri,
        content: Uint8Array,
        options: { create: boolean; overwrite: boolean }): void | Thenable<void> {
        throw vscode.FileSystemError.NoPermissions('JarFileSystemProvider is read-only');
    }

    delete(uri: vscode.Uri, options: { recursive: boolean }): void | Thenable<void> {
        throw vscode.FileSystemError.NoPermissions('JarFileSystemProvider is read-only');
    }

    rename(oldUri: vscode.Uri, newUri: vscode.Uri, options: { overwrite: boolean }): void | Thenable<void> {
        throw vscode.FileSystemError.NoPermissions('JarFileSystemProvider is read-only');
    }

    copy?(source: vscode.Uri, destination: vscode.Uri, options: { overwrite: boolean }): void | Thenable<void> {
        throw vscode.FileSystemError.NoPermissions('JarFileSystemProvider is read-only');
    }

    /**
     * Utility method to create a jarfile: URI
     * @param archivePath Path to the JAR/ZIP file
     * @param internalPath Path inside the archive
     */
    static createJarUri(archivePath: string, internalPath: string = ''): vscode.Uri {
        // Ensure the internal path starts with /
        const normalizedInternalPath = internalPath.startsWith('/') ? internalPath : '/' + internalPath;
        return vscode.Uri.parse(`jarfile:${archivePath}!${normalizedInternalPath}`);
    }

    /**
     * Clean up cached ZIP instances
     */
    dispose(): void {
        this.zipCache.clear();
        this._emitter.dispose();
    }
}
