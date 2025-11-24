import { test as base, expect } from '@playwright/test';
import { startFixtureServer, FixtureServer } from './support/server';

type Fixtures = {
    fixtureServer: FixtureServer;
};

const test = base.extend<Fixtures>({
    // eslint-disable-next-line @typescript-eslint/no-unused-vars, no-empty-pattern
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

        // Verify copy button click does not toggle the tree item
        const variableItem = page.locator('vscode-tree-item#state-1 vscode-tree-item').first();
        if (await variableItem.count() > 0) {
            const varBlock = variableItem.locator('.var-block');
            await varBlock.hover();
            const copyBtn = variableItem.locator('.codicon-copy');
            await expect(copyBtn).toBeVisible();
            
            // Ensure we don't toggle the item
            const wasOpen = await variableItem.evaluate(el => el.hasAttribute('open'));
            await copyBtn.click();
            const isOpen = await variableItem.evaluate(el => el.hasAttribute('open'));
            expect(isOpen).toBe(wasOpen);
        }

        // Move mouse away to ensure hover state is cleared (buttons hidden) before screenshot
        await page.mouse.move(0, 0);

        await expect(page.locator('vscode-tree')).toHaveScreenshot('error-trace.png');
    });
});
