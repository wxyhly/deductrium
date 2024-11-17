import { Hvec, Quaternion, Rotor } from "./algebra.js";
export class LocalDraw {
    lineStep = 10;
    horocycleStep = 10;
    scale = 0.99;
    canvas;
    ctxt;
    constructor(canvas) {
        this.canvas = canvas;
        this.ctxt = canvas.getContext("2d");
    }
    clear() {
        this.ctxt.clearRect(0, 0, this.canvas.width, this.canvas.height);
    }
    drawOutBorder() {
        this.ctxt.beginPath();
        this.ctxt.arc(this.canvas.width / 2, this.canvas.height / 2, this.scale * Math.min(this.canvas.width, this.canvas.height) / 2, 0, Math.PI * 2);
        this.ctxt.fill();
    }
    // drawPlayer() {
    //     this.ctxt.beginPath();
    //     this.ctxt.arc(this.canvas.width / 2, this.canvas.height / 2, 10*window.devicePixelRatio, 0, Math.PI * 2);
    //     this.ctxt.fill();
    // }
    moveTo(p) {
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        this.ctxt.moveTo(p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2);
    }
    lineTo(p) {
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        this.ctxt.lineTo(p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2);
    }
    textTo(p, text) {
        if (p.z > 1e2)
            return;
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        const fs = Math.round(25 * window.devicePixelRatio / p.z);
        this.ctxt.font = fs + "px sans-serif"; // + "px";
        const arr = text.split("\n");
        const middle = (arr.length - 1) / 2;
        for (const [id, row] of arr.entries()) {
            this.ctxt.fillText(row, p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2 + fs * ((id - middle) * 1.3 + 1 / 4));
        }
    }
    drawLine(p1, p2, lineTo) {
        const precalc = Hvec.precalcLerp(p1, p2);
        for (let k = 0; k <= this.lineStep; k++) {
            if (!k && !lineTo) {
                this.moveTo(p1);
                continue;
            }
            this.lineTo(Hvec.fastLerp(p1, p2, k / this.lineStep, precalc));
        }
    }
    drawPolygon(p, mat, debug) {
        const center = mat.apply(new Hvec);
        if (center.z > 1e3)
            return;
        this.ctxt.beginPath();
        let pa = debug ? new Hvec(p.vertex.z, p.vertex.x * 0.99, p.vertex.y * 0.99).normalize() : p.vertex;
        const r = Rotor.rotate(Math.PI * 2 / p.p);
        for (let i = 0; i < p.p; i++) {
            let pb = r.apply(pa);
            this.drawLine(mat.apply(pa), mat.apply(pb), true);
            pa = pb;
        }
        this.ctxt.fill();
        this.ctxt.beginPath();
        if (debug)
            this.drawLine(mat.apply(new Hvec(1, 0, 0.4)).normalize(), mat.apply(new Hvec(1, 0, 0.7)).normalize(), true);
        this.ctxt.stroke();
    }
    drawHoroRect(hr, mat) {
        this.ctxt.beginPath();
        // draw horocyle passing by (sh(l),0,ch(l))
        const len = hr.h / 2;
        const w_2 = hr.w / 2;
        let p = new Hvec(Math.cosh(len), 0, Math.sinh(len));
        let first = true;
        for (let k = -this.horocycleStep; k <= this.horocycleStep; k++) {
            const angle = w_2 * k / this.horocycleStep;
            if (first) {
                this.moveTo(mat.mul(new Rotor(1, angle, 0, angle)).apply(p));
                first = false;
            }
            else {
                this.lineTo(mat.mul(new Rotor(1, angle, 0, angle)).apply(p));
            }
        }
        let p2 = new Hvec(Math.cosh(len), 0, -Math.sinh(len));
        this.drawLine(mat.mul(new Rotor(1, w_2, 0, w_2)).apply(p), mat.mul(new Rotor(1, w_2, 0, w_2)).apply(p2), true);
        first = false;
        for (let k = -this.horocycleStep; k <= this.horocycleStep; k++) {
            const angle = w_2 * k / this.horocycleStep;
            if (first) {
                this.moveTo(mat.mul(new Rotor(1, -angle, 0, -angle)).apply(p2));
                first = false;
            }
            else {
                this.lineTo(mat.mul(new Rotor(1, -angle, 0, -angle)).apply(p2));
            }
        }
        this.drawLine(mat.mul(new Rotor(1, -w_2, 0, -w_2)).apply(p2), mat.mul(new Rotor(1, -w_2, 0, -w_2)).apply(p));
        this.ctxt.fill();
    }
    // }
    // class Charactor{
    points = [
        [1, 0, 0, 0], [0, 1, 0, 0], [-1, 0, 0, 0], [0, -1, 0, 0],
        [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, -1, 0], [0, 0, 0, -1],
    ];
    edges1 = [
        [0, 4], [4, 2], [6, 2], [6, 0],
        [1, 5], [5, 3], [7, 3], [7, 1],
    ];
    edges2 = [
        [0, 1], [1, 2], [2, 3], [3, 0],
        [4, 5], [5, 6], [6, 7], [7, 4],
    ];
    edges3 = [
        [0, 5], [5, 2], [2, 7], [7, 0],
        [1, 4], [4, 3], [3, 6], [6, 1],
    ];
    rotorL = Quaternion.rand();
    rotorR = Quaternion.rand();
    drawPlayer() {
        this.ctxt.beginPath();
        this.ctxt.arc(this.canvas.width / 2, this.canvas.height / 2, 10 * window.devicePixelRatio, 0, Math.PI * 2);
        this.ctxt.fill();
        const ps = this.points.map((p) => {
            const r = new Quaternion(...p);
            r.mulsl(this.rotorL).mulsr(this.rotorR);
            const p3 = 3;
            const p2 = 3;
            const scale = 3;
            // 3d perspect proj
            r.x *= (r.w + p3) / p3;
            r.y *= (r.w + p3) / p3;
            r.z *= (r.w + p3) / p3;
            // 2d perspect proj
            r.x *= (r.z + p2) / p2 * scale;
            r.y *= (r.z + p2) / p2 * scale;
            return [this.canvas.width / 2 + 20 * window.devicePixelRatio * r.x, this.canvas.height / 2 - 20 * window.devicePixelRatio * r.y];
        });
        this.ctxt.lineWidth = 1.5 * window.devicePixelRatio;
        this.ctxt.strokeStyle = "rgba(255,70,50,0.5)";
        this.ctxt.beginPath();
        for (const [a, b] of this.edges1) {
            this.ctxt.moveTo(ps[a][0], ps[a][1]);
            this.ctxt.lineTo(ps[b][0], ps[b][1]);
        }
        this.ctxt.stroke();
        this.ctxt.strokeStyle = "rgba(0,0,255,1)";
        this.ctxt.beginPath();
        for (const [a, b] of this.edges2) {
            this.ctxt.moveTo(ps[a][0], ps[a][1]);
            this.ctxt.lineTo(ps[b][0], ps[b][1]);
        }
        this.ctxt.stroke();
        this.ctxt.strokeStyle = "rgba(0,180,0,0.3)";
        this.ctxt.beginPath();
        for (const [a, b] of this.edges3) {
            this.ctxt.moveTo(ps[a][0], ps[a][1]);
            this.ctxt.lineTo(ps[b][0], ps[b][1]);
        }
        this.ctxt.stroke();
    }
}
//# sourceMappingURL=localdraw.js.map