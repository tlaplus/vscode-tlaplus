import { defineConfig, devices } from '@playwright/test';
import path from 'path';

export default defineConfig({
	testDir: path.join(__dirname, 'tests', 'playwright'),
	fullyParallel: false,
	workers: 1,
	timeout: 120_000,
	expect: {
		timeout: 15_000
	},
	use: {
		actionTimeout: 15_000,
		navigationTimeout: 60_000,
		headless: true,
		viewport: { width: 1400, height: 900 },
		ignoreHTTPSErrors: true,
		screenshot: 'only-on-failure',
		video: 'off',
		trace: 'on-first-retry',
		launchOptions: {
			args: ['--disable-dev-shm-usage', '--disable-extensions']
		}
	},
	reporter: [
		['list'],
		['html', { open: 'never', outputFolder: path.join('test-results', 'playwright-report') }]
	],
	projects: [
		{
			name: 'chromium',
			use: { ...devices['Desktop Chrome'], headless: true }
		}
	],
	outputDir: path.join(__dirname, 'test-results', 'playwright-output')
});
