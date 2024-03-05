import { mapData } from "./map.js"
export enum TileBlockType {
    Road, Wall, Gate, Reward
}
export type TileBlock = {
    type: TileBlockType,
    name: string,
    text: string,
}
export const blockMap = new Map<string, TileBlock>();
export const nameMap = new Map<string, string>();
mapData.split("\n:").map(e => e.replaceAll("\n", "")).forEach(e => {
    if(!e) return;
    let hash = "";
    let tbt: TileBlockType;
    let content = "";
    let header = true;
    for (const k of e) {
        if (!header) { content += k; continue; }
        const i = "@|#$".indexOf(k);
        if (i === -1) { hash += k; continue; }
        tbt = i;
        header = false;
    }
    const matched = content.match(/^\s*(\[\[(.+)\]\])?(.*)$/);
    const tb: TileBlock = { type: tbt, name: matched[2], text: matched[3].replaceAll("[n]", "\n") };
    blockMap.set(hash, tb);
    if (matched[2]) {
        nameMap.set(matched[2], hash);
    }
});