import * as assert from 'assert';
import { createTreeItemRegistry } from '../../../src/webview/checkResultView/errorTraceSection/treeItemRegistry';

suite('Tree Item Registry', () => {
    interface TestTreeItem {
        open: boolean;
    }

    test('collapseAll closes every registered item', () => {
        const registry = createTreeItemRegistry<TestTreeItem>();
        const first: TestTreeItem = {open: true};
        const second: TestTreeItem = {open: true};

        registry.register(0, first);
        registry.register(1, second);

        registry.collapseAll();

        assert.strictEqual(first.open, false);
        assert.strictEqual(second.open, false);
    });

    test('expandAll opens every registered item', () => {
        const registry = createTreeItemRegistry<TestTreeItem>();
        const first: TestTreeItem = {open: false};
        const second: TestTreeItem = {open: false};

        registry.register(0, first);
        registry.register(1, second);

        registry.expandAll();

        assert.strictEqual(first.open, true);
        assert.strictEqual(second.open, true);
    });

    test('register removes items when null is provided', () => {
        const registry = createTreeItemRegistry<TestTreeItem>();
        const item: TestTreeItem = {open: true};

        registry.register(0, item);
        registry.collapseAll();
        assert.strictEqual(item.open, false);

        registry.register(0, null);

        item.open = false;
        registry.expandAll();

        assert.strictEqual(item.open, false);
    });
});
