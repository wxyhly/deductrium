export class Hvec {
    x;
    y;
    z;
    constructor(z = 1, x = 0, y = 0) {
        this.x = x;
        this.z = z;
        this.y = y;
    }
    normalize() {
        const l = Math.sqrt(this.z * this.z - this.x * this.x - this.y * this.y);
        this.x /= l;
        this.y /= l;
        this.z /= l;
        return this;
    }
    dot(p) {
        return this.z * p.z - this.x * p.x - this.y * p.y;
    }
    cross(p) {
        // z-xy, x-zy, y-xz
        return new Hvec(this.x * p.y - this.y * p.x, this.z * p.y - this.y * p.z, this.x * p.z - this.z * p.x);
    }
    static precalcLerp(a, b) {
        const cosf = a.dot(b);
        if (Math.abs(cosf) > 1.0001) {
            let f = Math.acosh(cosf);
            let _1s = 1 / Math.sinh(f);
            return [f, _1s];
        }
    }
    static fastLerp(a, b, t, precalc) {
        if (!precalc) {
            return new Hvec(a.z + (b.z - a.z) * t, a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t);
        }
        else {
            const [f, _1s] = precalc;
            const tf = t * f;
            let ka;
            let kb;
            ka = Math.sinh(f - tf) * _1s;
            kb = Math.sinh(tf) * _1s;
            return new Hvec(a.z * ka + b.z * kb, a.x * ka + b.x * kb, a.y * ka + b.y * kb);
        }
    }
}
class Curve {
    o;
    // time-like: circle, null: horocyle, space-like: equidistcurve or straight line
    n;
}
export class Rotor {
    r;
    x;
    y;
    z;
    /** r:1, x: xz, y:yz, z:xy */
    constructor(r = 1, x = 0, y = 0, z = 0) {
        this.r = r;
        this.x = x;
        this.z = z;
        this.y = y;
    }
    clone() {
        return new Rotor(this.r, this.x, this.y, this.z);
    }
    static move(x, y) {
        const l = Math.hypot(x, y);
        const k1 = l > 0.0001 ? Math.sinh(l) / l : (1 - l * l / 6);
        const k2 = Math.cosh(l);
        return new Rotor(k2, x * k1, y * k1, 0);
    }
    static moveTo(target) {
        const lxy = Math.hypot(target.x, target.y);
        const l = Math.acosh(target.z) / 2;
        const k1 = l > 0.0001 ? Math.sinh(l) / lxy : (1 - lxy * lxy / 8) / 2; // sh(ash(x)/2)/x
        const k2 = Math.cosh(l);
        return new Rotor(k2, target.x * k1, target.y * k1, 0);
    }
    static rotateAround(o, theta) {
        const m = Rotor.moveTo(o);
        return m.mul(Rotor.rotate(theta)).mul(m.conj());
    }
    static rotate(z) {
        const k1 = Math.sin(z / 2);
        const k2 = Math.cos(z / 2);
        return new Rotor(k2, 0, 0, k1);
    }
    static idealRotateCW(x, y) {
        // k^2 = 0 => exp(k) = 1+k
        return new Rotor(1, x, y, Math.hypot(x, y));
    }
    static idealRotateCCW(x, y) {
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
    mul(r) {
        return new Rotor(this.r * r.r - this.z * r.z + this.x * r.x + this.y * r.y, this.x * r.r + this.r * r.x + this.y * r.z - this.z * r.y, this.y * r.r + this.r * r.y - this.x * r.z + this.z * r.x, this.z * r.r + this.r * r.z - this.x * r.y + this.y * r.x);
    }
    apply(p) {
        const q = this.mul(new Rotor(0, p.y, p.x, p.z)).mul(this.conj());
        return new Hvec(q.z, q.y, q.x);
    }
}
//# sourceMappingURL=algebra.js.map