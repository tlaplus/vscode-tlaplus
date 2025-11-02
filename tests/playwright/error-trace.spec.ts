import { test as base, expect } from '@playwright/test';
import fs from 'fs/promises';
import path from 'path';
import { startFixtureServer, FixtureServer } from './support/server';

type Fixtures = {
    fixtureServer: FixtureServer;
};

const test = base.extend<Fixtures>({
    fixtureServer: async ({}, use) => {
        const server = await startFixtureServer();
        try {
            await use(server);
        } finally {
            await server.dispose();
        }
    }
});

test.describe('Check Result webview fixture', () => {
    test('error trace tree wraps text and link does not collapse state', async ({ page, fixtureServer }) => {
        page.on('console', msg => {
            if (msg.type() === 'error') {
                console.error(`[fixture:${msg.type()}] ${msg.text()}`);
            }
        });

        await page.goto(fixtureServer.endpoint, { waitUntil: 'networkidle' });
        await page.addStyleTag({
            content: '* { transition-duration: 0s !important; animation-duration: 0s !important; }'
        });

        const state = page.locator('vscode-tree-item#state-1');
        await state.waitFor({ state: 'visible' });
        await expect(state).toHaveAttribute('open', '');
        const before = await state.evaluate(el => el.hasAttribute('open'));
        const stateLink = page.locator('vscode-tree-item#state-1 .error-trace-title button');
        await expect(stateLink).toHaveCount(1);
        await stateLink.click();
        const after = await state.evaluate(el => el.hasAttribute('open'));
        expect(after).toBe(before);

        const valueCell = page.locator('vscode-tree-item#state-1 .var-block .var-value').first();
        const whiteSpace = await valueCell.evaluate<string>(el => getComputedStyle(el).whiteSpace);
        expect(whiteSpace).toBe('normal');
        const overflowX = await valueCell.evaluate<string>(el => getComputedStyle(el).overflowX);
        expect(overflowX).toBe('visible');

        const screenshotDir = path.join('tests', 'playwright', 'snapshots');
        await fs.mkdir(screenshotDir, { recursive: true });
        await page.locator('vscode-tree').screenshot({
            path: path.join(screenshotDir, 'error-trace.png')
        });
    });
});
