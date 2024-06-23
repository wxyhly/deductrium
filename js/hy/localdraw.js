import { Hvec, Rotor } from "./algebra.js";
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
    drawPlayer() {
        this.ctxt.beginPath();
        this.ctxt.arc(this.canvas.width / 2, this.canvas.height / 2, 10, 0, Math.PI * 2);
        this.ctxt.fill();
    }
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
        const fs = Math.round(25 / p.z);
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
    drawPolygon(p, mat) {
        const center = mat.apply(new Hvec);
        if (center.z > 1e3)
            return;
        this.ctxt.beginPath();
        let pa = p.vertex;
        const r = Rotor.rotate(Math.PI * 2 / p.p);
        for (let i = 0; i < p.p; i++) {
            let pb = r.apply(pa);
            this.drawLine(mat.apply(pa), mat.apply(pb), true);
            pa = pb;
        }
        this.ctxt.fill();
        this.ctxt.beginPath();
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
}
//# sourceMappingURL=localdraw.js.map