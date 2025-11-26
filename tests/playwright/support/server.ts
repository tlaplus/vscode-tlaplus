import express from 'express';
import http from 'http';
import net, { AddressInfo } from 'net';
import path from 'path';

const REPO_ROOT = path.resolve(__dirname, '../../..');
const PUBLIC_ROOT = path.join(REPO_ROOT, 'tests', 'fixtures', 'playwright', 'public');
const DATA_ROOT = path.join(REPO_ROOT, 'tests', 'fixtures', 'playwright');
const OUT_ROOT = path.join(REPO_ROOT, 'out');

export interface FixtureServer {
	endpoint: string;
	dispose: () => Promise<void>;
}

export async function startFixtureServer(): Promise<FixtureServer> {
    const port = await getAvailablePort();
    const host = '127.0.0.1';
    const app = express();

    app.use('/static', express.static(OUT_ROOT));
    app.use('/data', express.static(DATA_ROOT));
    app.use('/', express.static(PUBLIC_ROOT, { extensions: ['html'] }));

    const server = await listenAsync(app, port, host);
    return {
        endpoint: `http://${host}:${port}/`,
        dispose: () =>
            new Promise((resolve, reject) => {
                server.close(err => {
                    if (err) {
                        reject(err);
                    } else {
                        resolve();
                    }
                });
            })
    };
}

function listenAsync(app: express.Express, port: number, host: string): Promise<http.Server> {
    return new Promise(resolve => {
        const server = app.listen(port, host, () => resolve(server));
    });
}

async function getAvailablePort(): Promise<number> {
    return await new Promise((resolve, reject) => {
        const server = net.createServer();
        server.unref();
        server.on('error', reject);
        server.listen(0, '127.0.0.1', () => {
            const address = server.address() as AddressInfo;
            server.close(err => {
                if (err) {
                    reject(err);
                } else {
                    resolve(address.port);
                }
            });
        });
    });
}
