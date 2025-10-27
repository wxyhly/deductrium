import { TTGui } from "./gui.js";

export class SavesParser {

    serialize(gui: TTGui) {
        const arrs = gui.getInhabitatArray().map(e => e.value);
        return JSON.stringify(arrs);
    }
    deserialize(gui: TTGui, s: string) {
        const arr = JSON.parse(s);
        for (const n of Array.from(gui.inhabitList.children)) {
            if (n.id !== "add-btn") n.remove();
        }
        arr.forEach(_ => gui.updateInhabitList());
        gui.getInhabitatArray().forEach(
            (e, idx) => { e.value = arr[idx]; }
        );
        gui.updateAfterUnlock();
        gui.getInhabitatArray()[0]?.onblur({} as any);
    }
}