export interface TreeItemWithOpen {
    open: boolean;
}

export interface TreeItemRegistry<T extends TreeItemWithOpen> {
    register: (index: number, item: T | null) => void;
    collapseAll: () => void;
    expandAll: () => void;
}

export const createTreeItemRegistry = <T extends TreeItemWithOpen>(): TreeItemRegistry<T> => {
    const treeItems = new Map<number, T>();

    const register = (index: number, item: T | null) => {
        if (item) {
            treeItems.set(index, item);
        } else {
            treeItems.delete(index);
        }
    };

    const setOpenForAll = (open: boolean) => {
        treeItems.forEach((treeItem) => {
            treeItem.open = open;
        });
    };

    return {
        register,
        collapseAll: () => setOpenForAll(false),
        expandAll: () => setOpenForAll(true)
    };
};
