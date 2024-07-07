import { Hvec, Rotor } from "./algebra.js";
import { LocalDraw } from "./localdraw.js";
import { TileBlock, TileBlockType, blockMap, initMap, nameMap } from "./maploader.js";
import { HoroRect, Polygon, TileHash, TileNeighbor } from "./tiling.js";

export class HWorld {
    debugDraw = false;
    localDraw: LocalDraw;
    localCamMat = new Rotor;
    currentTile: TileHash = [];
    gravity = true;
    highLightGetD = false;
    onPassGate: (hash: string, tile: TileBlock) => boolean;
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
        return blockMap.get(hash) ?? blockMap.get(nameMap.get(hash));
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
            else ctxt.fillStyle = ["rgb(255,255,255)", "rgb(220,220,220)", "rgb(250,160,20)", "rgb(200,255,20)"][block?.type ?? 1];
            this.localDraw.drawPolygon(this.atlasTile, this.localCamMat.mul(r), this.debugDraw);
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
            ctxt.fillStyle = ["rgb(0,80,0)", "rgb(60,60,255)", "rgb(33,38,255)", "rgb(255,0,0)"][block.type];
            this.localDraw.textTo(this.localCamMat.mul(r).apply(new Hvec), block.text);
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
            this.hitReward(b, t.join(","));
            return true;
        }
        if (b.type === TileBlockType.Gate) {
            return this.onPassGate(b.name, b);
        }
    }
    hitReward(b: TileBlock, hash: string, isLoading?: boolean) {
        this.onGetReward(b.name ?? hash, b, isLoading);
        if (b.type !== TileBlockType.Gate) {
            b.text = "已" + b.text;
        }
        b.type = TileBlockType.Road;
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