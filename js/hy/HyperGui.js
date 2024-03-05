import { Rotor, Hvec, Polygon } from "./algebra.js";
export class HyperGui {
    canvas;
    ctxt;
    camMat;
    polygonStep = 20;
    scale = 0.95;
    constructor(canvas) {
        this.canvas = canvas;
        this.ctxt = this.canvas.getContext("2d");
        this.canvas.onresize = () => { onresize; };
        this.onLoop();
    }
    onresize() {
        this.canvas.width = this.canvas.clientWidth;
        this.canvas.height = this.canvas.clientHeight;
    }
    moveTo(p) {
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        this.ctxt.moveTo(p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2);
    }
    lineTo(p) {
        const scale = this.scale / (p.z + 1) * Math.min(this.canvas.width, this.canvas.height) / 2;
        this.ctxt.lineTo(p.x * scale + this.canvas.width / 2, p.y * scale + this.canvas.height / 2);
    }
    drawPolygon(p, mat) {
        let pa = p.vertex.normalize();
        const r = Rotor.rotate(Math.PI * 2 / p.p);
        for (let i = 0; i < p.p; i++) {
            let pb = r.apply(pa);
            let mpa = mat.apply(pa);
            let mpb = mat.apply(pb);
            const precalc = Hvec.precalcLerp(mpa, mpb);
            for (let k = 0; k <= this.polygonStep; k++) {
                if (!k) {
                    this.moveTo(mpa);
                    continue;
                }
                // this.moveTo(pa);
                this.lineTo(Hvec.fastLerp(mpa, mpb, k / this.polygonStep, precalc));
            }
            pa = pb;
        }
    }
    drawOutBorder() {
        this.ctxt.beginPath();
        this.ctxt.fillStyle = "rgb(230,230,230)";
        this.ctxt.arc(this.canvas.width / 2, this.canvas.height / 2, this.scale * Math.min(this.canvas.width, this.canvas.height) / 2, 0, Math.PI * 2);
        this.ctxt.fill();
    }
    clear() {
        this.ctxt.clearRect(0, 0, this.canvas.width, this.canvas.height);
    }
    onLoop() {
        this.clear();
        this.drawOutBorder();
        this.ctxt.beginPath();
        this.ctxt.strokeStyle = "solid";
        const p = new Polygon(7, 6);
        this.drawPolygon(p, new Rotor);
        this.drawPolygon(p, Rotor.move());
        this.ctxt.stroke();
    }
}
//# sourceMappingURL=HyperGui.js.map