import * as assert from 'assert';
import * as vscode from 'vscode';
import { buildSpectacleHtml } from '../../../src/commands/openSpectacle';

suite('Open Spectacle command', () => {
    test('buildSpectacleHtml injects CSP, base URI, and nonces', () => {
        const extension = vscode.extensions.getExtension('tlaplus.vscode-ide');
        assert.ok(extension, 'Extension metadata should be available during tests');

        const stubWebview = {
            cspSource: 'vscode-resource://test',
            asWebviewUri: (uri: vscode.Uri) => uri,
        } as unknown as vscode.Webview;

        const html = buildSpectacleHtml(stubWebview, extension.extensionUri);

        assert.ok(html.includes('<base href="'), 'Base tag should be injected for webview resources');
        assert.ok(html.includes('Content-Security-Policy'), 'CSP meta tag should be present');
        assert.ok(html.includes('window.SPECTACLE_BASE_URL'), 'Spectacle base URL bootstrap script should be injected');

        const scriptsMissingNonce = html.match(/<script(?![^>]*nonce=)/g);
        assert.strictEqual(scriptsMissingNonce, null, 'Every script tag should carry a nonce attribute');
    });
});
