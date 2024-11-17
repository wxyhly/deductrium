export class Vec {
    x: number; y: number; z: number;
    constructor(z: number = 0, x: number = 0, y: number = 0) {
        this.x = x; this.z = z; this.y = y;
    }
    norm() {
        const l = Math.sqrt(this.z * this.z + this.x * this.x + this.y * this.y);
        return l;
    }
}
export class Hvec {
    x: number; y: number; z: number;
    constructor(z: number = 1, x: number = 0, y: number = 0) {
        this.x = x; this.z = z; this.y = y;
    }
    normalize() {
        const l = Math.sqrt(this.z * this.z - this.x * this.x - this.y * this.y);
        this.x /= l;
        this.y /= l;
        this.z /= l;
        return this;
    }
    dot(p: Hvec) {
        return this.z * p.z - this.x * p.x - this.y * p.y;
    }
    cross(p: Hvec) {
        // z-xy, x-zy, y-xz
        return new Hvec(this.x * p.y - this.y * p.x, this.z * p.y - this.y * p.z, this.x * p.z - this.z * p.x);
    }
    static precalcLerp(a: Hvec, b: Hvec) {
        const cosf = a.dot(b);
        if (Math.abs(cosf) > 1.0001) {
            let f = Math.acosh(cosf);
            let _1s = 1 / Math.sinh(f);
            return [f, _1s];
        }
    }
    static fastLerp(a: Hvec, b: Hvec, t: number, precalc: number[]) {
        if (!precalc) {
            return new Hvec(a.z + (b.z - a.z) * t, a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t);
        } else {
            const [f, _1s] = precalc;
            const tf = t * f;
            let ka: number; let kb: number;
            ka = Math.sinh(f - tf) * _1s;
            kb = Math.sinh(tf) * _1s;
            return new Hvec(a.z * ka + b.z * kb, a.x * ka + b.x * kb, a.y * ka + b.y * kb);
        }
    }
}
class Curve {
    o: number;
    // time-like: circle, null: horocyle, space-like: equidistcurve or straight line
    n: Hvec;

}

export class Rotor {
    r: number; x: number; y: number; z: number;
    /** r:1, x: xz, y:yz, z:xy */
    constructor(r: number = 1, x: number = 0, y: number = 0, z: number = 0,) {
        this.r = r; this.x = x; this.z = z; this.y = y;
    }
    clone() {
        return new Rotor(this.r, this.x, this.y, this.z);
    }
    static move(x: number, y: number) {
        const l = Math.hypot(x, y);
        const k1 = l > 0.0001 ? Math.sinh(l) / l : (1 - l * l / 6);
        const k2 = Math.cosh(l);
        return new Rotor(k2, x * k1, y * k1, 0);
    }
    static moveTo(target: Hvec) {
        const lxy = Math.hypot(target.x, target.y);
        const l = Math.acosh(target.z) / 2;
        const k1 = l > 0.0001 ? Math.sinh(l) / lxy : (1 - lxy * lxy / 8) / 2; // sh(ash(x)/2)/x
        const k2 = Math.cosh(l);
        return new Rotor(k2, target.x * k1, target.y * k1, 0);
    }
    static rotateAround(o: Hvec, theta: number) {
        const m = Rotor.moveTo(o);
        return m.mul(Rotor.rotate(theta)).mul(m.conj());
    }
    static rotate(z: number) {
        const k1 = Math.sin(z / 2);
        const k2 = Math.cos(z / 2);
        return new Rotor(k2, 0, 0, k1);
    }
    static idealRotateCW(x: number, y: number) {
        // k^2 = 0 => exp(k) = 1+k
        return new Rotor(1, x, y, Math.hypot(x, y));
    }
    static idealRotateCCW(x: number, y: number) {
        // k^2 = 0 => exp(k) = 1+k
        return new Rotor(1, x, y, -Math.hypot(x, y));
    }
    normalize() {
        const l = Math.sqrt(this.r * this.r + this.z * this.z - this.x * this.x - this.y * this.y);
        this.x /= l;
        this.y /= l;
        this.z /= l;
        this.r /= l;
        return this;
    }
    conj() {
        return new Rotor(this.r, -this.x, -this.y, -this.z);
    }
    mul(r: Rotor) {
        return new Rotor(
            this.r * r.r - this.z * r.z + this.x * r.x + this.y * r.y,
            this.x * r.r + this.r * r.x + this.y * r.z - this.z * r.y,
            this.y * r.r + this.r * r.y - this.x * r.z + this.z * r.x,
            this.z * r.r + this.r * r.z - this.x * r.y + this.y * r.x,
        );
    }
    apply(p: Hvec) {
        const q = this.mul(new Rotor(0, p.y, p.x, p.z)).mul(this.conj());
        return new Hvec(q.z, q.y, q.x);
    }
}
// from repo tesserxel
export class Quaternion {
    x: number;
    y: number;
    z: number;
    w: number;
    constructor(x: number = 1, y: number = 0, z: number = 0, w: number = 0) {
        this.x = x; this.y = y; this.z = z; this.w = w;
    }
    set(x: number = 1, y: number = 0, z: number = 0, w: number = 0) {
        this.x = x; this.y = y; this.z = z; this.w = w; return this;
    }
    flat(): number[] {
        return [this.x, this.y, this.z, this.w];
    }
    copy(v: Quaternion) {
        this.x = v.x; this.y = v.y;
        this.z = v.z; this.w = v.w;
        return this;
    }
    clone(): Quaternion {
        return new Quaternion(this.x, this.y, this.z, this.w);
    }

    neg(): Quaternion {
        return new Quaternion(-this.x, -this.y, -this.z, -this.w);
    }
    negs(): Quaternion {
        this.x = - this.x; this.y = -this.y; this.z = -this.z; this.w = -this.w;
        return this;
    }
    mul(q: Quaternion): Quaternion {
        return new Quaternion(
            this.x * q.x - this.y * q.y - this.z * q.z - this.w * q.w,
            this.x * q.y + this.y * q.x + this.z * q.w - this.w * q.z,
            this.x * q.z - this.y * q.w + this.z * q.x + this.w * q.y,
            this.x * q.w + this.y * q.z - this.z * q.y + this.w * q.x
        );
    }
    /** this = this * q; */
    mulsr(q: Quaternion): Quaternion {
        var x = this.x * q.x - this.y * q.y - this.z * q.z - this.w * q.w;
        var y = this.x * q.y + this.y * q.x + this.z * q.w - this.w * q.z;
        var z = this.x * q.z - this.y * q.w + this.z * q.x + this.w * q.y;
        this.w = this.x * q.w + this.y * q.z - this.z * q.y + this.w * q.x;
        this.x = x; this.y = y; this.z = z; return this;
    }
    /** this = q * this; */
    mulsl(q: Quaternion): Quaternion {
        var x = q.x * this.x - q.y * this.y - q.z * this.z - q.w * this.w;
        var y = q.x * this.y + q.y * this.x + q.z * this.w - q.w * this.z;
        var z = q.x * this.z - q.y * this.w + q.z * this.x + q.w * this.y;
        this.w = q.x * this.w + q.y * this.z - q.z * this.y + q.w * this.x;
        this.x = x; this.y = y; this.z = z; return this;
    }
    /** this = this * conj(q); */
    mulsrconj(q: Quaternion): Quaternion {
        var x = this.x * q.x + this.y * q.y + this.z * q.z + this.w * q.w;
        var y = -this.x * q.y + this.y * q.x - this.z * q.w + this.w * q.z;
        var z = -this.x * q.z + this.y * q.w + this.z * q.x - this.w * q.y;
        this.w = -this.x * q.w - this.y * q.z + this.z * q.y + this.w * q.x;
        this.x = x; this.y = y; this.z = z; return this;
    }
    /** this = conj(q) * this; */
    mulslconj(q: Quaternion): Quaternion {
        var x = q.x * this.x + q.y * this.y + q.z * this.z + q.w * this.w;
        var y = q.x * this.y - q.y * this.x - q.z * this.w + q.w * this.z;
        var z = q.x * this.z + q.y * this.w - q.z * this.x - q.w * this.y;
        this.w = q.x * this.w - q.y * this.z + q.z * this.y - q.w * this.x;
        this.x = x; this.y = y; this.z = z; return this;
    }
    conj(): Quaternion {
        return new Quaternion(this.x, -this.y, -this.z, -this.w);
    }
    conjs(): Quaternion {
        this.y = -this.y; this.z = -this.z; this.w = -this.w; return this;
    }
    norm(): number {
        return Math.sqrt(this.x * this.x + this.y * this.y + this.z * this.z + this.w * this.w);
    }
    norms(): Quaternion {
        let n = Math.sqrt(this.x * this.x + this.y * this.y + this.z * this.z + this.w * this.w);
        n = n == 0 ? 0 : (1 / n);
        this.x *= n; this.y *= n; this.z *= n; this.w *= n; return this;
    }
    static expset(xy: number, xz: number, xw: number, yz: number, yw: number, zw: number) {
        let A = new Vec(xy + zw, xz - yw, xw + yz);
        let B = new Vec(xy - zw, xz + yw, xw - yz);
        let a = A.norm(); let b = B.norm();
        let aa = a * 0.5; let bb = b * 0.5;
        let sa = (a > 0.005 ? Math.sin(aa) / a : 0.5 - a * a / 12);
        let sb = (b > 0.005 ? Math.sin(bb) / b : 0.5 - b * b / 12);
        return [
            new Quaternion(Math.cos(aa), sa * A.x, sa * A.y, sa * A.z),
            new Quaternion(Math.cos(bb), sb * B.x, sb * B.y, sb * B.z)
        ];
    }
    static rand(): Quaternion {
        let a = Math.random() * Math.PI * 2;
        let b = Math.random() * Math.PI * 2;
        let c = Math.random();
        let sc = Math.sqrt(c);
        let cc = Math.sqrt(1 - c);
        return new Quaternion(sc * Math.cos(a), sc * Math.sin(a), cc * Math.cos(b), cc * Math.sin(b));
    }
}