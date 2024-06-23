import { Hvec, Rotor } from "./algebra.js";
import { CosetTable } from "./group.js";
export class Polygon {
    p;
    q; // {p,q}
    n1;
    n2;
    n3; // 3 reflect planes normals
    vertex; // vertex in foundamental domain
    edge; // edge center in foundamental domain
    R; // R^p = e
    I; // I^2 = e, 
    invR; // (RI)^q = e
    cosetTable;
    rotors;
    neighborMatrix = [];
    // rotors: Rotor[];
    constructor(p, q) {
        this.p = p;
        this.q = q;
        const t1 = Math.PI / p;
        const t2 = Math.PI / q;
        this.n1 = new Hvec(0, Math.cos(t1), Math.sin(t1));
        this.n2 = new Hvec(0, 1, 0);
        const chs = Math.cos(t2) / Math.sin(t1);
        const shs = Math.sqrt(chs * chs - 1);
        this.n3 = new Hvec(shs, 0, chs);
        this.vertex = this.n1.cross(this.n3).normalize();
        this.edge = this.n2.cross(this.n3).normalize();
        this.R = Rotor.rotate(2 * t1);
        this.invR = this.R.conj();
        this.I = Rotor.rotateAround(this.edge, Math.PI);
        this.cosetTable = new CosetTable("ri", ["ii", "r".repeat(this.p), "ir".repeat(this.q)], ["r"]);
        let moveR = Rotor.moveTo(this.edge);
        moveR = moveR.mul(moveR);
        for (let i = 0; i < this.p; i++) {
            this.neighborMatrix.push(Rotor.rotate(t1 * i * 2).mul(moveR).mul(Rotor.rotate(Math.PI)));
        }
    }
    isInDomain(p) {
        for (let i = 0; i < this.p; i++) {
            if (Rotor.rotate(-Math.PI * 2 * i / this.p).apply(p).dot(this.n3) < 0)
                return i;
        }
        return -1;
    }
    generateRotorsByToddCoxter() {
        const cosetTable = this.cosetTable;
        const rs = new Array(cosetTable.length);
        rs[0] = new Rotor;
        for (const [c, coset] of cosetTable.cosets.entries()) {
            const r = rs[c];
            for (const [x, cx] of coset.entries()) {
                if (rs[cx])
                    continue;
                const g = x === 0 ? this.R : x === 1 ? this.invR : this.I;
                rs[cx] = g.mul(r);
                continue;
            }
        }
        // this.rotors = rs;
    }
    generateRotors(t = []) {
        const maxNums = 512;
        const frontiers = [t];
        this.rotors = new Map([[t.join(","), new Rotor]]);
        let f;
        while ((f = frontiers.pop()) && this.rotors.size < maxNums) {
            for (let i = 0; i < this.p; i++) {
                const [nf, dir] = this.getNeighborAndDir(f, i, true);
                const str = nf.join(",");
                if (this.rotors.has(str))
                    continue;
                this.rotors.set(str, this.rotors.get(f.join(",")).mul(this.getNeighborMatrix(dir, i)));
                frontiers.unshift(nf);
            }
        }
    }
    getState(t, idx) {
        if (!t.length)
            return 0;
        if (idx === 0)
            return 1;
        const tidx = t[idx];
        if (this.q === 3) {
            if (tidx > 3)
                return 1; //short circuit to avoid recursion
            if (this.getState(t, idx - 1) === 1)
                return tidx === 2 ? 2 : 1;
            else
                return tidx === 3 ? 2 : 1;
        }
        if (this.q === 4) {
            if (tidx > 2)
                return 1; //short circuit to avoid recursion
            if (this.getState(t, idx - 1) === 1)
                return tidx === 1 ? 2 : 1;
            else
                return tidx === 2 ? 2 : 1;
        }
    }
    getNeighborAndDir(t, n, copy) {
        if (n < 0) {
            n += this.p;
        }
        if (n >= this.p) {
            n -= this.p;
        }
        if (this.q !== 4 && this.q !== 3)
            throw "not implemented yet";
        if (copy)
            t = t.slice(0);
        // state 0
        if (!t.length) {
            t.push(n);
            return [t, 0];
        }
        // state 1/2
        if (n === 0) {
            return [t, t.pop()];
        }
        if (n === this.p - 1) {
            const pn = t.pop() + 1;
            const dir = this.getNeighborAndDir(t, pn, false)[1];
            if (this.q === 4) {
                const nd = this.getNeighborAndDir(t, dir + 1, false)[1];
                return [t, nd + 1];
            }
            if (this.q === 3) {
                return [t, dir + 1];
            }
        }
        if (this.q === 3 && n === this.p - 2) {
            this.getNeighborAndDir(t, this.p - 1, false);
            const state1 = this.getState(t, t.length - 1) === 1;
            t.push(state1 ? 2 : 3);
            return [t, 1];
        }
        const state1 = this.getState(t, t.length - 1) === 1;
        if (state1) {
            // state 1
            if (n === 1) {
                if (this.q === 4) {
                    t.push(n);
                    return [t, 0];
                }
                if (this.q === 3) {
                    const pn = t.pop() - 1;
                    this.getNeighborAndDir(t, pn, false);
                    return [t, this.p - 1];
                }
            }
        }
        else {
            // state 2
            if (n === 1) {
                if (this.q === 4) {
                    let pn = t.pop();
                    let dir = this.getNeighborAndDir(t, pn - 1, false)[1];
                    dir = this.getNeighborAndDir(t, dir - 1, false)[1];
                    return [t, dir - 1];
                }
                if (this.q === 3) {
                    const pn = t.pop() - 1;
                    const dir = this.getNeighborAndDir(t, pn, false)[1];
                    return [t, dir - 1];
                }
            }
            if (this.q === 3 && n === 2) {
                this.getNeighborAndDir(t, 1, false);
                t.push(this.p - 3);
                return [t, this.p - 1];
            }
        }
        t.push(n);
        return [t, 0];
    }
    getNeighborMatrix(dir, n) {
        return this.neighborMatrix[n].mul(Rotor.rotate(-dir * 2 * Math.PI / this.p));
    }
}
const TileParent = 0;
const TileLeft = -1;
const TileRight = -2;
export class HoroRect {
    // p: tree branchs
    p;
    // w: tree width
    w;
    // h: tree height (generated by p)
    h;
    upperBound;
    lowerBound;
    leftBoundNormal;
    rightBoundNormal;
    branchBoundNormals = [];
    rotors = new Map;
    constructor(p, w) {
        this.p = p;
        this.w = w;
        this.h = Math.log(p);
        this.upperBound = Math.cosh(this.h / 2) - Math.sinh(this.h / 2);
        this.lowerBound = Math.cosh(this.h / 2) + Math.sinh(this.h / 2);
        this.leftBoundNormal = new Rotor(1, this.w / 2, 0, this.w / 2).apply(new Hvec(0, 1, 0));
        this.rightBoundNormal = new Rotor(1, -this.w / 2, 0, -this.w / 2).apply(new Hvec(0, 1, 0));
        for (let k = 1; k < p; k++) {
            this.branchBoundNormals.push(new Rotor(1, -this.w / this.p * k, 0, -this.w / this.p * k).apply(this.leftBoundNormal));
        }
    }
    generateRotors(t = []) {
        const maxNums = 1024;
        const frontiers = [t];
        this.rotors = new Map([[t.join(","), new Rotor]]);
        let f;
        while ((f = frontiers.pop()) && this.rotors.size < maxNums) {
            for (let i = -2; i <= this.p; i++) {
                // const i=-2;
                const nf = this.getNeighbor(f, i, true);
                const str = nf.join(",");
                if (this.rotors.has(str))
                    continue;
                this.rotors.set(str, this.rotors.get(f.join(",")).mul(this.getNeighborMatrix(this.getIndex(f), i)));
                frontiers.unshift(nf);
            }
        }
    }
    // return the tile's index in its siblings
    getIndex(t, slice = t.length - 1) {
        if (t[slice] > 0)
            return t[slice];
        return ((slice + 1) % this.p) + 1;
    }
    getNeighbor(t, n, copy) {
        if (copy)
            t = t.slice(0);
        if (n > 0) {
            if (t[t.length - 1] === 0) {
                if (n === ((t.length - 1) % this.p) + 1) {
                    t.pop();
                    return t;
                }
            }
            t.push(n);
            return t;
        }
        if (n === TileParent) {
            if (t[t.length - 1] > 0)
                t.pop();
            else
                t.push(n);
            return t;
        }
        if (n === TileLeft) {
            const idx = this.getIndex(t);
            if (idx > 1)
                return this.getNeighbor(this.getNeighbor(t, TileParent, copy), idx - 1, false);
            return this.getNeighbor(this.getNeighbor(this.getNeighbor(t, TileParent, copy), TileLeft, false), this.p, false);
        }
        if (n === TileRight) {
            const idx = this.getIndex(t);
            if (idx < this.p)
                return this.getNeighbor(this.getNeighbor(t, TileParent, copy), idx + 1, false);
            return this.getNeighbor(this.getNeighbor(this.getNeighbor(t, TileParent, copy), TileRight, false), 1, false);
        }
        throw "cannot reach";
    }
    getNeighborMatrix(idx, n) {
        if (n === TileLeft) {
            return new Rotor(1, this.w, 0, this.w);
        }
        if (n === TileRight) {
            return new Rotor(1, -this.w, 0, -this.w);
        }
        if (n > 0) {
            const delta = n - (1 + this.p) / 2;
            return Rotor.move(0, -this.h / 2).mul(new Rotor(1, -this.w * delta, 0, -this.w * delta));
            // return new Rotor(1, -this.w * delta, 0, -this.w * delta).mul(Rotor.move(0, -this.h / 2));
        }
        if (n === 0) {
            const delta = (1 + this.p) / 2 - idx;
            // return Rotor.move(0, this.h / 2).mul(new Rotor(1, this.w * delta, 0, this.w * delta));
            return new Rotor(1, -this.w * delta, 0, -this.w * delta).mul(Rotor.move(0, this.h / 2));
        }
    }
    getAtlasMatrix(src, dst) {
        // [a2b,b2c,c2d]
        const words = [];
        // [aidx,bidx,cidx,didx]
        const wordsIndex = [this.getIndex(src)];
        // pushAndReduce: idx is pushed, but words not
        const pushAndReduce = (n) => {
            const l = words.length;
            if (!l) {
                words.push(n);
                return;
            }
            const prev = words[l - 1];
            const prevIdx = wordsIndex[l - 1];
            // canceled
            const cancel = (prev > 0 && n === 0) || (prev === 0 && n === prevIdx) || (prev === TileLeft && n === TileRight) || (prev === TileRight && n === TileLeft);
            if (cancel) {
                words.pop();
                wordsIndex.pop();
                wordsIndex.pop();
                return;
            }
            // atomic left/right
            if (prev === 0) {
                if (prevIdx > 0 && prevIdx + 1 === n) {
                    words.pop();
                    words.push(TileRight);
                    const lastId = wordsIndex.pop();
                    wordsIndex.pop();
                    wordsIndex.push(lastId);
                    return;
                }
                if (n > 0 && n + 1 === prevIdx) {
                    words.pop();
                    words.push(TileLeft);
                    const lastId = wordsIndex.pop();
                    wordsIndex.pop();
                    wordsIndex.push(lastId);
                    return;
                }
            }
            // recursive left/right
            const prev2 = words[l - 2];
            if (n === 1 && prev2 === 0 && prev === TileRight && wordsIndex[l - 2] === this.p) {
                words.pop();
                words.pop();
                words.push(TileRight);
                const lastId = wordsIndex.pop();
                wordsIndex.pop();
                wordsIndex.pop();
                wordsIndex.push(lastId);
                return;
            }
            if (n === 1 && prev2 === 0 && prev === TileRight && wordsIndex[l - 2] === this.p) {
                words.pop();
                words.pop();
                words.push(TileLeft);
                const lastId = wordsIndex.pop();
                wordsIndex.pop();
                wordsIndex.pop();
                wordsIndex.push(lastId);
                return;
            }
            // otherwise no rule for reducing
            words.push(n);
        };
        // inverse src
        for (let i = src.length - 1; i >= 0; i--) {
            wordsIndex.push(this.getIndex(src, i - 1));
            if (src[i] > 0) {
                pushAndReduce(0);
                continue;
            } // if go to child, inv: go parent
            if (src[i] === 0) { // if go to parent, inv: go to child
                pushAndReduce(this.getIndex(src, i - 1));
                continue;
            }
            throw "cannot reached";
        }
        // dst
        for (let i = 0; i < dst.length; i++) {
            wordsIndex.push(this.getIndex(dst, i));
            pushAndReduce(dst[i]);
        }
        let r = new Rotor;
        for (const [l, w] of words.entries()) {
            // r = r.mul(this.getNeighborMatrix(wordsIndex[l],w));
            // r = r.mul(this.getNeighborMatrix(wordsIndex[l],w).conj());
            // r = this.getNeighborMatrix(wordsIndex[l],w).mul(r);
            r = this.getNeighborMatrix(wordsIndex[l], w).conj().mul(r);
        }
        return r;
    }
}
//# sourceMappingURL=tiling.js.map