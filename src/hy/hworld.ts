import { Hvec, Rotor } from "./algebra.js";
import { LocalDraw } from "./localdraw.js";
import { TileBlock, TileBlockType, blockMap, initMap, nameMap } from "./maploader.js";
import { genOrdTiles } from "./ordinal.js";
import { Polygon, TileHash } from "./tiling.js";

export class HWorld {
    debugDraw = false;
    navigateDraw = false;
    localDraw: LocalDraw;
    localCamMat = new Rotor;
    currentTile: TileHash = [];
    currentOrd: number[] = null;
    gravity = true;
    highLightGetD = false;
    // if tile doesn't have name, name is hash
    onPassGate: (name: string, tile: TileBlock, hash: string) => boolean;
    onGetReward: (hash: string, tile: TileBlock, isLoading?: boolean) => void;
    onStateChange = () => { };
    onStepToAnotherTile = () => { };
    atlasTile: Polygon;
    constructor(canvas: HTMLCanvasElement) {
        this.localDraw = new LocalDraw(canvas);
        this.atlasTile = new Polygon(6, 4);
        this.atlasTile.generateRotors();
        initMap(this.atlasTile);
    }
    getBlock(hash: string) {
        const r = blockMap.get(hash) ?? blockMap.get(nameMap.get(hash));
        if (!r && hash.startsWith("1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,3,3")) {
            if (hash.match(/^1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,3,3,(3|4(,2)*,1)/)) {
                const stone = hash.match(/2,3$/);
                const k = "卍般摩波慧迦莲净空寂禅佛孤於婆玄冥尔智超菩提修皈灵尊弥咒唵噜嘿噶吽萨魅魂丧魄心戒律缚摒幽乾刹伽吒禄衰阳阴若陀";
                return { type: stone ? 2 : hash.match(/(3|4(,2)*,1)...+(2|4),(3|4(,2)*,1)/) ? 4 : hash.match(/((3,3)|(4,4)|(2,2))$/) ? 3 : 0, name: undefined, text: stone ? k[(hash.length * 31 + hash.lastIndexOf("2") * 53 + hash.lastIndexOf("3") * 11 + 3) % k.length] : "" };
            }
        }
        return r;
    }
    getNamedBlockHash(name: string) {
        return nameMap.get(name);
    }
    onLoop() {
        const ctxt = this.localDraw.ctxt;
        this.localDraw.clear();
        ctxt.fillStyle = "rgb(220,220,220)";
        this.localDraw.drawOutBorder();
        ctxt.textAlign = "center";
        ctxt.fillStyle = "rgb(0,0,255)";

        for (const [s, r] of this.atlasTile.rotors) {
            const block = this.getBlock(s);
            if (!block && !this.debugDraw) continue;
            if (this.highLightGetD && block?.text?.match(/^获取(.+)推理素$/)) ctxt.fillStyle = "rgb(255,255,0)";
            else ctxt.fillStyle = ["rgb(255,255,255)", "rgb(220,220,220)", "rgb(250,160,20)", "rgb(200,255,20)", "rgb(180,255,240)"][block?.type ?? 1];
            this.localDraw.drawPolygon(this.atlasTile, this.localCamMat.mul(r), this.navigateDraw);
        }
        for (const [s, r] of this.atlasTile.rotors) {
            const block = this.getBlock(s);
            if (!block) {
                if (this.debugDraw) {
                    ctxt.fillStyle = "rgb(0,0,0)";
                    this.localDraw.textTo(this.localCamMat.mul(r).apply(new Hvec), s);
                }
                continue;
            }
            ctxt.fillStyle = ["rgb(0,80,0)", "rgb(60,60,255)", "rgb(33,38,255)", "rgb(255,0,0)", "rgb(30,20,100)"][block.type];
            let text = block.text;
            if (true) {
                if (text.endsWith("#p") || text.endsWith("#d")) {
                    text = text.replaceAll("V", "∀").replaceAll("<>", "↔").replaceAll(/E([^q])/g, "∃$1").replaceAll("@", "∈").replaceAll("~", "¬")
                        .replaceAll(">", " → ").replaceAll("<", "⊂").replaceAll("U", "∪").replaceAll("I", "∩")
                        .replaceAll("&", "∧").replaceAll("|", "∨").replaceAll("omega", "ω")
                } else if (text.endsWith("#t")) {
                    text = text.replaceAll("->", " → ").replaceAll("L", "λ").replaceAll("S", "Σ").replaceAll("P", "Π")
                        .replaceAll("X", "×").replaceAll("|", "∨")
                }
            }
            this.localDraw.textTo(this.localCamMat.mul(r).apply(new Hvec), text);
        }
        ctxt.fillStyle = "rgb(0,0,0)";
        this.localDraw.drawPlayer();
    }
    hitTest(t: TileHash) {
        // return true;
        const b = this.getBlock(t.join(','));
        if (!b || b.type === TileBlockType.Wall) return false;
        if (b.type === TileBlockType.Road) return true;
        if (b.type === TileBlockType.Reward) {
            if (b.text) this.hitReward(b, t.join(","));
            return true;
        }
        if (b.type === TileBlockType.Gate || b.type === TileBlockType.Ordinal) {
            return this.onPassGate(b.name ?? t.join(','), b, t.join(','));
        }
    }
    hitReward(b: TileBlock, hash: string, isLoading?: boolean) {
        this.onGetReward(b.name ?? hash, b, isLoading);
        if (b.type !== TileBlockType.Gate) {
            b.text = "已" + b.text;
        }
        b.type = TileBlockType.Road;
    }
    onPassOrd(hash: string, ord: number[]) {
        genOrdTiles(blockMap, nameMap, this.atlasTile, hash.split(",").map(e => Number(e)), ord);
    }
    moveCam(x: number, y: number) {
        this.localCamMat = Rotor.move(x, y).mul(this.localCamMat).normalize();
        const pos = this.localCamMat.conj().apply(new Hvec);
        this.onStateChange();
        const newDomain = this.atlasTile.isInDomain(pos);
        if (newDomain !== -1) {
            const [newHash, dir] = this.atlasTile.getNeighborAndDir(this.currentTile, newDomain, true);
            const hitTest = this.hitTest(newHash);
            if (!hitTest) {
                const normal = this.localCamMat.conj().mul(Rotor.rotate(- Math.PI * 2 * newDomain / this.atlasTile.p)).apply(this.atlasTile.n3);
                const theta = Math.atan2(normal.y, normal.x); const ds = Math.hypot(x, y);
                this.localCamMat = Rotor.move(Math.cos(theta) * ds - x, Math.sin(theta) * ds - y).mul(this.localCamMat);
            } else {
                this.onStepToAnotherTile();
                const r = this.atlasTile.getNeighborMatrix(dir, newDomain);
                this.atlasTile.generateRotors(newHash);
                this.localCamMat = this.localCamMat.mul(r);
                this.currentTile = newHash;
            }
        }
    }
}