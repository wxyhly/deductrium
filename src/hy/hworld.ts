import { Hvec, Rotor } from "./algebra.js";
import { LocalDraw } from "./localdraw.js";
import { TileBlock, TileBlockType, blockMap } from "./maploader.js";
import { HoroRect, Polygon, TileHash, TileNeighbor } from "./tiling.js";

export class HWorld {
    localDraw: LocalDraw;
    localCamMat = new Rotor;
    atlasTile: HoroRect;
    currentTile: TileHash = [];
    gravity = true;
    onPassGate: (hash: string, tile: TileBlock) => boolean;
    onGetReward: (hash: string, tile: TileBlock) => void;

    test:Polygon;
    constructor(canvas: HTMLCanvasElement) {
        this.localDraw = new LocalDraw(canvas);
        this.atlasTile = new HoroRect(3, 1);
        this.test=new Polygon(7,3);
        this.toggleAtlas([], new Rotor);
    }
    getBlock(hash: string) {
        return blockMap.get(hash);
    }
    onLoop() {
        const ctxt = this.localDraw.ctxt;
        this.localDraw.clear();
        ctxt.fillStyle = "rgb(220,220,220)";
        this.localDraw.drawOutBorder();
        ctxt.textAlign = "center";
        for (const [s, r] of this.atlasTile.rotors) {
            const block = this.getBlock(s); if (!block) continue;
            ctxt.fillStyle = ["rgb(255,255,255)", "rgb(220,220,220)", "rgb(200,90,80)", "rgb(200,255,20)"][block.type];
            this.localDraw.drawHoroRect(this.atlasTile, this.localCamMat.mul(r));
        }
        for (const [s, r] of this.atlasTile.rotors) {
            const block = this.getBlock(s);
            if (!block) {
                ctxt.fillStyle = "rgb(0,0,0)";
                this.localDraw.textTo(this.localCamMat.mul(r).apply(new Hvec), s); continue;
            }
            ctxt.fillStyle = ["rgb(0,0,255)", "rgb(60,60,255)", "rgb(255,255,80)", "rgb(255,0,0)"][block.type];
            this.localDraw.textTo(this.localCamMat.mul(r).apply(new Hvec), block.text);
        }
        // this.ctxt.fillStyle = "rgb(255,0,0)";

        // for (const [t, p, s] of this.texts) {
        //     this.textTo(this.camMat.mul(this.horoRect.getAtlasMatrix(t, this.currentTile)).apply(p), s);
        //     // this.textTo( this.horoRect.getAtlasMatrix(t, this.currentTile).mul(this.camMat).apply(p), s);
        // }
    }
    hitTest(t: TileHash, n: TileNeighbor) {
        const b = this.getBlock(t.join(','));
        if (!b || b.type === TileBlockType.Wall) return false;
        if (b.type === TileBlockType.Road) return true;
        if (b.type === TileBlockType.Reward) {
            this.onGetReward(b.name, b);
            b.type = TileBlockType.Road;
            b.text = "已" + b.text;
            return true;
        }
        if (b.type === TileBlockType.Gate) {
            return this.onPassGate(b.name, b);
        }
    }
    moveCam(x: number, y: number) {
        this.localCamMat = Rotor.move(x, y).mul(this.localCamMat).normalize();


        // check if need move to new atlas

        const pos = this.localCamMat.conj().apply(new Hvec);
        if (pos.z - pos.y < this.atlasTile.upperBound) {
            if (!this.toggleTileNeighborAtlas(0)) {
                this.localCamMat = Rotor.move(0, -2 * y).mul(this.localCamMat);
            }
        }
        if (pos.z - pos.y > this.atlasTile.lowerBound) {
            let neighbor = this.atlasTile.p;
            for (const [b, normal] of this.atlasTile.branchBoundNormals.entries()) {
                if (normal.dot(pos) > 0) { neighbor = b + 1; break; }
            }
            if (!this.toggleTileNeighborAtlas(neighbor)) {
                this.localCamMat = Rotor.move(0, -2 * y).mul(this.localCamMat);
            }
        }
        if (this.atlasTile.leftBoundNormal.dot(pos) > 0) {
            if (!this.toggleTileNeighborAtlas(-1)) {
                this.localCamMat = Rotor.move(-2 * x, 0).mul(this.localCamMat);
            }
        }
        if (this.atlasTile.rightBoundNormal.dot(pos) < 0) {
            if (!this.toggleTileNeighborAtlas(-2)) {
                this.localCamMat = Rotor.move(-2 * x, 0).mul(this.localCamMat);
            }
        }

        if (this.gravity) {
            const inside = this.localCamMat.apply(new Hvec(1, 0, 1));
            this.localCamMat = Rotor.rotate(Math.atan2(-inside.x, inside.y)).mul(this.localCamMat);
        }
    }
    toggleTileNeighborAtlas(n: TileNeighbor) {
        const r = this.atlasTile.getNeighborMatrix(this.atlasTile.getIndex(this.currentTile), n);
        const newHash = this.atlasTile.getNeighbor(this.currentTile, n, true);
        const hitTest = this.hitTest(newHash, n);
        if (hitTest) this.toggleAtlas(newHash, r);
        return hitTest;
    }
    toggleAtlas(t: TileHash, r: Rotor) {
        this.atlasTile.generateRotors(t);
        this.localCamMat = this.localCamMat.mul(r);
        this.currentTile = t;
    }
}