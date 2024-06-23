export class SavesParser {
    serialize(gui) {
        const arrs = gui.getInhabitatArray().map(e => e.value);
        return JSON.stringify(arrs);
    }
    deserialize(gui, s) {
        const arr = JSON.parse(s);
        for (const n of Array.from(gui.inhabitList.children)) {
            if (n.id !== "add-btn")
                n.remove();
        }
        arr.forEach(_ => gui.updateInhabitList());
        gui.getInhabitatArray().forEach((e, idx) => { e.value = arr[idx]; e.onblur({}); });
    }
}
//# sourceMappingURL=savesparser.js.map