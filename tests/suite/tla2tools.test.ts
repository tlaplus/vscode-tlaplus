import * as assert from 'assert';
import { buildJavaOptions, buildTlcOptions, buildPlusCalOptions } from '../../src/tla2tools';

suite('TLA+ Tools Test Suite', () => {

    test('Builds PlusCal options with no custom settings', () => {
        assert.deepEqual(
            buildPlusCalOptions('/path/to/module.tla', []),
            ['/path/to/module.tla']
        );
    });

    test('Puts PlusCal custom options before module name', () => {
        assert.deepEqual(
            buildPlusCalOptions('/path/to/module.tla', ['-lineWidth', '100', '-nocfg']),
            ['-lineWidth', '100', '-nocfg', '/path/to/module.tla']
        );
    });

    test('Provides default TLC options', () => {
        assert.deepEqual(
            buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', []),
            ['/path/to/module.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/module.cfg']
        );
    });

    test('Adds custom TLC options', () => {
        assert.deepEqual(
            buildTlcOptions('/path/to/module.tla', '/path/to/module.cfg', ['-deadlock', '-checkpoint', '5']),
            ['/path/to/module.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/module.cfg',
            '-deadlock', '-checkpoint', '5']
        );
    });

    test('Allows to change module .cfg in TLC options', () => {
        assert.deepEqual(
            buildTlcOptions(
                '/path/to/module.tla',
                '/path/to/module.cfg',
                ['-deadlock', '-config', '/path/to/another.cfg', '-nowarning']
            ), [
                '/path/to/module.tla', '-tool', '-modelcheck', '-coverage', '1', '-config', '/path/to/another.cfg',
                '-deadlock', '-nowarning'
            ]
        );
    });

    test('Allows to change coverage in TLC options', () => {
        assert.deepEqual(
            buildTlcOptions(
                '/path/to/module.tla',
                '/path/to/module.cfg',
                ['-deadlock', '-coverage', '2', '-nowarning']
            ), [
                '/path/to/module.tla', '-tool', '-modelcheck', '-coverage', '2', '-config', '/path/to/module.cfg',
                '-deadlock', '-nowarning'
            ]
        );
    });

    test('Provides default GC in Java options', () => {
        assert.deepEqual(buildJavaOptions([]), ['-XX:+UseParallelGC']);
    });

    test('Adds custom Java options', () => {
        assert.deepEqual(
            buildJavaOptions(['-Xmx2048M', '-Xms512M']),
            ['-Xmx2048M', '-Xms512M', '-XX:+UseParallelGC']
        );
    });

    test('Allows to change default GC via Java options', () => {
        assert.deepEqual(
            buildJavaOptions(['-Xmx2048M', '-XX:+UseG1GC', '-Xms512M']),
            ['-Xmx2048M', '-XX:+UseG1GC', '-Xms512M']
        );
    });
});
