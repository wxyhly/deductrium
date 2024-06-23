import { Rotor } from "./algebra.js";
import { HWorld } from "./hworld.js";

export class SavesParser {
    serialize(w: HWorld) {
        const thash = w.currentTile.join(",");
        const pos = w.localCamMat;
        return thash + `:${pos.r.toPrecision(4)},${pos.x.toPrecision(4)},${pos.y.toPrecision(4)},${pos.z.toPrecision(4)}`;
    }
    deserialize(w: HWorld,s: string) {
        const [thash, pos] = s.split(":");
        w.currentTile = thash ? thash.split(",").map(n => Number(n)) : [];
        w.atlasTile.generateRotors(w.currentTile);
        w.localCamMat = new Rotor(...pos.split(",").map(n => Number(n)));
    }
}