import { langMgr } from "../lang.js";
import { mapData } from "./map.js";
import { genOrdTiles } from "./ordinal.js";
export var TileBlockType;
(function (TileBlockType) {
    TileBlockType[TileBlockType["Road"] = 0] = "Road";
    TileBlockType[TileBlockType["Wall"] = 1] = "Wall";
    TileBlockType[TileBlockType["Gate"] = 2] = "Gate";
    TileBlockType[TileBlockType["Reward"] = 3] = "Reward";
    TileBlockType[TileBlockType["Ordinal"] = 4] = "Ordinal";
})(TileBlockType || (TileBlockType = {}));
export const blockMap = new Map();
export const nameMap = new Map();
let prevTilehash = null;
export function initMap(p) {
    genOrdTiles(blockMap, nameMap, p, [1, 2, 1], [1], 5);
    mapData.split("\n").map(e => e.trimStart().replaceAll("\n", "")).forEach(e => {
        if (!e)
            return;
        if (e.startsWith("//"))
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
            const i = "@|#$O".indexOf(k);
            if (i === -1) {
                hash += k;
                continue;
            }
            tbt = i;
            header = false;
        }
        let t = [];
        const parent = hash.match(/^\:([^,]+),/);
        if (parent && parent[1]) {
            hash = hash.replace(/^\:([^,]+),/, "");
            if (parent[1] === "%") {
                t = prevTilehash;
            }
            else if (parent[1] === "%*") {
                t = prevTilehash.slice(0);
            }
            else {
                t = nameMap.get(parent[1]).split(",").map(e => e ? Number(e) : NaN);
            }
        }
        if (hash.includes(";")) {
            for (const s of hash.split(";")) {
                if (!s)
                    continue;
                p.getNeighborAndDir(t, Number(s), false);
                const tb = { type: tbt, name: undefined, text: "" };
                blockMap.set(t.join(","), tb);
            }
            if (!(parent && parent[1] === "%*"))
                prevTilehash = t;
            return;
        }
        if (hash)
            for (const s of hash.split(",")) {
                p.getNeighborAndDir(t, Number(s), false);
            }
        const matched = content.match(/^\s*(\[\[(.+)\]\])?(.*)$/);
        const tb = { type: tbt, name: matched[2], text: matched[3].replaceAll("[n]", "\n") };
        blockMap.set(t.join(","), tb);
        if (matched[2]) {
            nameMap.set(matched[2], t.join(","));
        }
        if (!(parent && parent[1] === "%*"))
            prevTilehash = t;
    });
    // console.log(Array.from(blockMap.values()).filter(e=>e.type!=TileBlockType.Ordinal&&(e.text.startsWith("["))));
    console.log(JSON.stringify(Array.from(blockMap.values()).map(e => langMgr.trc1(langMgr.trc(e.text))).filter(e => (/[\u4e00-\u9fa5]/.test(e)))));
    // console.log(JSON.stringify(Array.from(blockMap.values()).filter(e=>(/[\u4e00-\u9fa5]/.test(e.text))).map(e=>e.text)));
}
//# sourceMappingURL=maploader.js.map