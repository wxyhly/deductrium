import { Hvec, Quaternion, Rotor } from "./algebra.js";
import { HoroRect, Polygon } from "./tiling.js";

export class LocalDraw {
    lineStep = 10;
    horocycleStep = 10;
    scale = 0.99;
    canvas: HTMLCanvasElement;
    ctxt: CanvasRenderingContext2D;
    constructor(canvas: HTMLCanvasElement) {
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
    moveTo(p: Hvec) {
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        this.ctxt.moveTo(p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2);
    }
    lineTo(p: Hvec) {
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        this.ctxt.lineTo(p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2);
    }
    textTo(p: Hvec, text: string) {
        if (p.z > 1e2) return;
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        const fs = Math.round(25 * window.devicePixelRatio / p.z);
        this.ctxt.font = fs + "px sans-serif";// + "px";
        const arr = text.split("\n");
        const middle = (arr.length - 1) / 2;
        for (const [id, row] of arr.entries()) {
            this.ctxt.fillText(row, p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2 + fs * ((id - middle) * 1.3 + 1 / 4));
        }
    }
    drawLine(p1: Hvec, p2: Hvec, lineTo?: boolean) {
        const precalc = Hvec.precalcLerp(p1, p2);
        for (let k = 0; k <= this.lineStep; k++) {
            if (!k && !lineTo) { this.moveTo(p1); continue; }
            this.lineTo(Hvec.fastLerp(p1, p2, k / this.lineStep, precalc));
        }
    }
    drawPolygon(p: Polygon, mat: Rotor, debug: boolean) {
        const center = mat.apply(new Hvec);
        if (center.z > 1e3) return;
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
        if (debug) this.drawLine(mat.apply(new Hvec(1, 0, 0.4)).normalize(), mat.apply(new Hvec(1, 0, 0.7)).normalize(), true);
        this.ctxt.stroke();
    }
    drawHoroRect(hr: HoroRect, mat: Rotor) {
        this.ctxt.beginPath();
        // draw horocyle passing by (sh(l),0,ch(l))
        const len = hr.h / 2;
        const w_2 = hr.w / 2;
        let p = new Hvec(Math.cosh(len), 0, Math.sinh(len));
        let first = true;
        for (let k = -this.horocycleStep; k <= this.horocycleStep; k++) {
            const angle = w_2 * k / this.horocycleStep;
            if (first) {
                this.moveTo(mat.mul(new Rotor(1, angle, 0, angle)).apply(p)); first = false;
            } else {
                this.lineTo(mat.mul(new Rotor(1, angle, 0, angle)).apply(p));
            }
        }
        let p2 = new Hvec(Math.cosh(len), 0, -Math.sinh(len));
        this.drawLine(mat.mul(new Rotor(1, w_2, 0, w_2)).apply(p), mat.mul(new Rotor(1, w_2, 0, w_2)).apply(p2), true);
        first = false;
        for (let k = -this.horocycleStep; k <= this.horocycleStep; k++) {
            const angle = w_2 * k / this.horocycleStep;
            if (first) {
                this.moveTo(mat.mul(new Rotor(1, -angle, 0, -angle)).apply(p2)); first = false;
            } else {
                this.lineTo(mat.mul(new Rotor(1, -angle, 0, -angle)).apply(p2));
            }
        }
        this.drawLine(mat.mul(new Rotor(1, -w_2, 0, -w_2)).apply(p2), mat.mul(new Rotor(1, -w_2, 0, -w_2)).apply(p));
        this.ctxt.fill();
    }
    // }
    // class Charactor{
    pointsA: number[][] = [
        [1, 0, 0, 0], [0, 1, 0, 0], [-1, 0, 0, 0], [0, -1, 0, 0],
        [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, -1, 0], [0, 0, 0, -1],
    ];
    pointsB: number[][] = [[0.000, 0.373, -0.659, 0.510], [-0.323, -0.186, -0.659, 0.510], [0.000, 0.745, -0.132, 0.510], [0.323, -0.186, -0.659, 0.510], [-0.323, 0.559, 0.395, 0.510], [-0.645, -0.373, -0.132, 0.510], [0.000, 0.745, -0.527, 0.000], [0.323, 0.559, 0.395, 0.510], [-0.645, -0.000, 0.395, 0.510], [-0.323, 0.559, -0.395, -0.510], [0.645, -0.373, -0.132, 0.510], [-0.645, -0.373, -0.527, 0.000], [-0.323, -0.559, 0.395, 0.510], [0.323, 0.559, -0.395, -0.510], [0.645, -0.000, 0.395, 0.510], [-0.645, -0.000, -0.395, -0.510], [0.645, -0.373, -0.527, 0.000], [-0.645, 0.373, 0.527, 0.000], [0.323, -0.559, 0.395, 0.510], [-0.323, -0.559, -0.395, -0.510], [0.645, -0.000, -0.395, -0.510], [-0.645, 0.373, 0.132, -0.510], [0.645, 0.373, 0.527, 0.000], [0.323, -0.559, -0.395, -0.510], [-0.323, 0.186, 0.659, -0.510], [0.645, 0.373, 0.132, -0.510], [-0.000, -0.745, 0.527, 0.000], [0.323, 0.186, 0.659, -0.510], [-0.000, -0.745, 0.132, -0.510], [-0.000, -0.373, 0.659, -0.510]];

    edges1: [number, number][] = [
        [0, 4], [4, 2], [6, 2], [6, 0],
        [1, 5], [5, 3], [7, 3], [7, 1],
    ];
    edges2: [number, number][] = [
        [0, 1], [1, 2], [2, 3], [3, 0],
        [4, 5], [5, 6], [6, 7], [7, 4],
    ];

    edges3: [number, number][] = [
        [0, 5], [5, 2], [2, 7], [7, 0],
        [1, 4], [4, 3], [3, 6], [6, 1],
    ];
    edgesA: [number, number][] = [[0, 1], [0, 3], [2, 4], [1, 3], [2, 7], [5, 8], [6, 9], [4, 7], [5, 12], [6, 13], [10, 14], [11, 15], [8, 12], [9, 13], [10, 18], [11, 19], [16, 20], [17, 21], [14, 18], [15, 19], [16, 23], [17, 24], [22, 25], [20, 23], [21, 24], [22, 27], [26, 28], [25, 27], [26, 29], [28, 29]];
    edgesB: [number, number][] = [[0, 2], [1, 5], [0, 6], [3, 10], [4, 8], [1, 11], [2, 6], [7, 14], [3, 16], [9, 15], [4, 17], [5, 11], [12, 18], [13, 20], [7, 22], [9, 21], [8, 17], [10, 16], [19, 23], [13, 25], [12, 26], [15, 21], [14, 22], [24, 27], [19, 28], [18, 26], [20, 25], [24, 29], [23, 28], [27, 29]];
    rotorL = Quaternion.rand();
    rotorR = Quaternion.rand();
    drawPlayer() {
        this.ctxt.beginPath();
        this.ctxt.arc(this.canvas.width / 2, this.canvas.height / 2, 10 * window.devicePixelRatio, 0, Math.PI * 2);
        this.ctxt.fill();
        const change = (new Date().getHours() < 12) === ((new Date().getDate() & 2) === 1);
        const ps = (change ? this.pointsA : this.pointsB).map((p) => {
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
            return [this.canvas.width / 2 + 20 * window.devicePixelRatio * r.x, this.canvas.height / 2 - 20 * window.devicePixelRatio * r.y]
        });
        this.ctxt.lineWidth = 1.5 * window.devicePixelRatio;
        if (change) {
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
        } else {
            this.ctxt.strokeStyle = "rgba(0,170,0,0.4)";
            this.ctxt.beginPath();
            for (const [a, b] of this.edgesA) {
                this.ctxt.moveTo(ps[a][0], ps[a][1]);
                this.ctxt.lineTo(ps[b][0], ps[b][1]);
            }
            this.ctxt.stroke();

            this.ctxt.strokeStyle = "rgba(120,100,80,0.8)";
            this.ctxt.beginPath();
            for (const [a, b] of this.edgesB) {
                this.ctxt.moveTo(ps[a][0], ps[a][1]);
                this.ctxt.lineTo(ps[b][0], ps[b][1]);
            }
            this.ctxt.stroke();
        }
    }
}