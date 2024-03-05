import { mapData } from "./map.js";
export var TileBlockType;
(function (TileBlockType) {
    TileBlockType[TileBlockType["Road"] = 0] = "Road";
    TileBlockType[TileBlockType["Wall"] = 1] = "Wall";
    TileBlockType[TileBlockType["Gate"] = 2] = "Gate";
    TileBlockType[TileBlockType["Reward"] = 3] = "Reward";
})(TileBlockType || (TileBlockType = {}));
export const blockMap = new Map();
export const nameMap = new Map();
mapData.split("\n:").map(e => e.replaceAll("\n", "")).forEach(e => {
    if (!e)
        return;
    let hash = "";
    let tbt;
    let content = "";
    let header = true;
    for (const k of e) {
        if (!header) {
            content += k;
            continue;
        }
        const i = "@|#$".indexOf(k);
        if (i === -1) {
            hash += k;
            continue;
        }
        tbt = i;
        header = false;
    }
    const matched = content.match(/^\s*(\[\[(.+)\]\])?(.*)$/);
    const tb = { type: tbt, name: matched[2], text: matched[3].replaceAll("[n]", "\n") };
    blockMap.set(hash, tb);
    if (matched[2]) {
        nameMap.set(matched[2], hash);
    }
});
//# sourceMappingURL=maploader.js.map