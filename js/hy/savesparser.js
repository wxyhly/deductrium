import { Rotor } from "./algebra.js";
export class SavesParser {
    serialize(w) {
        const thash = w.currentTile.join(",");
        const pos = w.localCamMat;
        return thash + `:${pos.r.toPrecision(4)},${pos.x.toPrecision(4)},${pos.y.toPrecision(4)},${pos.z.toPrecision(4)}:${w.currentOrd?.join(",") ?? ''}`;
    }
    deserialize(w, s) {
        const [thash, pos, currentOrd] = s.split(":");
        w.currentTile = thash ? thash.split(",").map(n => Number(n)) : [];
        w.atlasTile.generateRotors(w.currentTile);
        w.localCamMat = new Rotor(...pos.split(",").map(n => Number(n)));
        w.currentOrd = currentOrd === "" ? [] : currentOrd.split(",").map(n => Number(n));
        for (let i = 1; i < w.currentOrd.length; i++) {
            const subOrd = w.currentOrd.slice(0, i);
            w.onPassOrd(w.getNamedBlockHash("O" + subOrd.join(",")), subOrd);
        }
    }
}
//# sourceMappingURL=savesparser.js.map