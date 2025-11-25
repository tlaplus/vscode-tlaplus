const { test, expect } = require('@playwright/test');
const http = require('http');
const fs = require('fs');
const path = require('path');

function startStaticServer(rootDir) {
    return new Promise((resolve, reject) => {
        const server = http.createServer((req, res) => {
            const requestPath = decodeURIComponent((req.url || '/').split('?')[0]);
            const normalizedPath = path.normalize(path.join(rootDir, requestPath));
            if (!normalizedPath.startsWith(rootDir)) {
                res.statusCode = 404;
                return res.end();
            }

            let targetPath = normalizedPath;
            if (fs.existsSync(targetPath) && fs.statSync(targetPath).isDirectory()) {
                targetPath = path.join(targetPath, 'index.html');
            }

            fs.readFile(targetPath, (err, data) => {
                if (err) {
                    res.statusCode = 404;
                    res.end();
                    return;
                }
                res.setHeader('Content-Type', getMimeType(targetPath));
                res.end(data);
            });
        });

        server.on('error', reject);
        server.listen(0, '127.0.0.1', () => {
            const address = server.address();
            resolve({
                server,
                url: `http://127.0.0.1:${address.port}/index.html`
            });
        });
    });
}

function getMimeType(filePath) {
    if (filePath.endsWith('.js')) {
        return 'application/javascript';
    }
    if (filePath.endsWith('.css')) {
        return 'text/css';
    }
    if (filePath.endsWith('.svg')) {
        return 'image/svg+xml';
    }
    if (filePath.endsWith('.json')) {
        return 'application/json';
    }
    if (filePath.endsWith('.wasm')) {
        return 'application/wasm';
    }
    if (filePath.endsWith('.ttf')) {
        return 'font/ttf';
    }
    if (filePath.endsWith('.html')) {
        return 'text/html';
    }
    return 'application/octet-stream';
}

test.describe('Spectacle bundle smoke test', () => {
    /** @type {http.Server} */
    let server;
    let baseUrl;

    test.beforeAll(async () => {
        const rootDir = path.resolve(__dirname, '../../resources/spectacle');
        const result = await startStaticServer(rootDir);
        server = result.server;
        baseUrl = result.url;
    });

    test.afterAll(async () => {
        await new Promise((resolve) => server.close(resolve));
    });

    async function bootstrapWebview(page) {
        await page.addInitScript(() => {
            window.__vscodeMessages = [];
            window.acquireVsCodeApi = () => ({
                postMessage: (message) => {
                    window.__vscodeMessages.push(message);
                }
            });
        });

        await page.goto(baseUrl);

        await page.waitForFunction(() => {
            return Array.isArray(window.__vscodeMessages) &&
                window.__vscodeMessages.some((msg) => msg && msg.type === 'spectacle:webview-ready');
        }, null, { timeout: 20000 });
    }

    test('renders a VS Code injected spec', async ({ page }) => {
        await bootstrapWebview(page);

        await page.evaluate(() => {
            const spec = `---- MODULE Playwright ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n====`;
            window.postMessage({ type: 'spectacle:init', specText: spec, specUri: 'file:///Playwright.tla' }, '*');
        });

        await page.getByText('Root module').waitFor({ timeout: 20000 });
        await expect(page.getByText('Playwright.tla')).toBeVisible();
    });

    test('steps through a PlusCal squares spec without eval errors', async ({ page }) => {
        await bootstrapWebview(page);

        const specPath = path.resolve(__dirname, '../fixtures/spectacle/squares.tla');
        const specText = fs.readFileSync(specPath, 'utf8');

        await page.evaluate((spec) => {
            window.postMessage({ type: 'spectacle:init', specText: spec, specUri: 'file:///squares.tla' }, '*');
        }, specText);

        const initialState = page.locator('[data-testid="next-state-choice"]').first();
        await initialState.waitFor({ timeout: 20000 });
        await initialState.click();

        const actionChoice = page.locator('.action-choice-name').filter({ hasText: 'Lbl_1' }).first();
        await actionChoice.waitFor({ timeout: 20000 });
        await actionChoice.click();

        const errorBanner = page.getByText('Error computing next states.');
        await expect(errorBanner).toBeHidden();

        const traceStates = page.locator('[data-testid="trace-state-elem"]');
        await expect(traceStates).toHaveCount(2);
    });
});
