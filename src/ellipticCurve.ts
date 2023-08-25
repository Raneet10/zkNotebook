import { PrimeField } from "./primeField";
import { ExtensionField, ExtensionFieldOverFq } from "./extensionField";
const sqrt = require("bigint-isqrt");

export interface PointOverFp {
    x: bigint;
    y: bigint;
    z: bigint;
}

export interface PointOverFq {
    x: bigint[];
    y: bigint[];
    z: bigint[];
}

export interface PointOverFqOverFq {
    x: bigint[][];
    y: bigint[][];
    z: bigint[][];
}

// TODO: Implement Schoof's algorithm
// function Schoof_algorithm(a: bigint, b: bigint, p: bigint){
//     let S = [];
//     let acc = 1n;
//     let prime = 1;
//     while (acc <= 4n * sqrt(p)) {
//         while (Math.isPrime(prime)
//         S.push(acc);
//         acc *= 2n;
//     }
// }

// /*
//     * Elliptic curve over Fp
//     * y² = x³ + a·x + b
//     * a, b are Fp elements
//     * 4·a³ + 27·b² != 0
//     * p is prime
//     */
export class EllipticCurveOverFp {
    readonly a: bigint;
    readonly b: bigint;
    readonly Fp: PrimeField;

    constructor(a: bigint, b: bigint, field: PrimeField) {
        const firstSummand = field.mul(4n, field.exp(a, 3n));
        const secondSummand = field.mul(27n, field.exp(b, 2n));
        const sum = field.add(firstSummand, secondSummand);
        if (field.eq(sum, field.zero)) {
            throw new Error("The curve is singular, choose another a and b");
        }

        this.a = a;
        this.b = b;
        this.Fp = field;
    }

    // Public Accessors
    get zero(): null {
        return null;
    }

    // Comparators
    eq(P: PointOverFp, Q: PointOverFp): boolean {
        return this.Fp.eq(P.x,Q.x) && this.Fp.eq(P.y,Q.y) && this.Fp.eq(P.z, Q.z);
    }

    neq(P: PointOverFp, Q: PointOverFp): boolean {
        return !this.eq(P, Q);
    }

    // Check if a point is the identity element
    is_zero(P: PointOverFp): boolean {
        return P === this.zero;
    }

    make_affine(P: PointOverFp) {
        let x_aff = this.Fp.div(P.x, this.Fp.mul(P.z, P.z))
        let y_aff = this.Fp.div(P.y, this.Fp.mul(this.Fp.mul(P.z, P.z), P.z))
        P.x = x_aff
        P.y = y_aff
        P.z = this.Fp.one
    }

    // Check that a point is on the curve
    is_on_curve(P: PointOverFp): boolean {
        this.make_affine(P)
        if (this.is_zero(P)) {
            return true;
        }

        const left_side = this.Fp.exp(P.y, 2n);
        const right_side = this.Fp.add(
            this.Fp.add(this.Fp.exp(P.x, 3n), this.Fp.mul(this.a, P.x)),
            this.b
        );

        return this.Fp.eq(left_side, right_side);
    }

    // Basic Arithmetic
    add(P: PointOverFp, Q: PointOverFp): PointOverFp {
        if (this.is_zero(P)) return Q;

        if (this.is_zero(Q)) return P;

        // How to handle this in Jacobian ?
        if (P.x === Q.x) {
            if (P.y !== Q.y) {
                // P = -Q
                return this.zero;
            }
        }

        // let m: bigint;
        // if (P.x === Q.x && P.y === Q.y) {
        //     m = this.Fp.div(
        //         this.Fp.add(this.Fp.mul(3n, this.Fp.mul(P.x, P.x)), this.a),
        //         this.Fp.mul(2n, P.y)
        //     );
        // } else {
        //     m = this.Fp.div(this.Fp.sub(Q.y, P.y), this.Fp.sub(Q.x, P.x));
        // }

        // const x = this.Fp.sub(this.Fp.sub(this.Fp.mul(m, m), P.x), Q.x);
        // const y = this.Fp.sub(this.Fp.mul(m, this.Fp.sub(P.x, x)), P.y);
        // return { x, y };
        
        if (this.eq(P, Q)) {
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
            let a = this.Fp.mul(P.x, P.x)
            let b = this.Fp.mul(P.y, P.y)
            let c = this.Fp.mul(b, b)
            let x1plusb = this.Fp.add(P.x, b)
            let x1plusbsq = this.Fp.mul(x1plusb, x1plusb)
            let d = this.Fp.mul(2n, this.Fp.sub(this.Fp.sub(x1plusbsq, a), b))
            let e = this.Fp.mul(3n, a)
            let f = this.Fp.mul(e, e)
            const x = this.Fp.sub(f, this.Fp.mul(2n, d))
            const y = this.Fp.sub(this.Fp.mul(e, this.Fp.sub(d, x)), this.Fp.mul(8n, c))
            const z = this.Fp.mul(2n, this.Fp.mul(P.y, P.z))
            return {x, y, z}
        } else {
            // https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
            let z1z1 = this.Fp.mul(P.z, P.z)
            let z2z2 = this.Fp.mul(Q.z, Q.z)
            let u1 = this.Fp.mul(P.x, z2z2)
            let u2 = this.Fp.mul(Q.x, z1z1)
            let s1 = this.Fp.mul(P.y, this.Fp.mul(Q.z, z2z2))
            let s2 = this.Fp.mul(Q.y, this.Fp.mul(P.z, z1z1))
            let h = this.Fp.sub(u2, u1)
            let hsq = this.Fp.mul(2n, h)
            let i = this.Fp.mul(hsq, hsq)
            let j = this.Fp.mul(h, i)
            let r = this.Fp.mul(2n, this.Fp.sub(s2, s1))
            let v = this.Fp.mul(u1, i)
            const x = this.Fp.sub(this.Fp.mul(r, r), this.Fp.sub(j, this.Fp.mul(2n, v)))
            const y = this.Fp.sub(this.Fp.mul(r, this.Fp.sub(v, x)), this.Fp.mul(2n, this.Fp.mul(s1, j)))
            let z1z2 = this.Fp.add(P.z, Q.z)
            let z1z2sq = this.Fp.mul(z1z2, z1z2)
            const z = this.Fp.mul(h, this.Fp.sub(this.Fp.sub(z1z2sq, z1z1), z2z2))
            return {x, y, z};
        }
    }

    sub(P: PointOverFp, Q: PointOverFp): PointOverFp {
        return this.add(P, this.neg(Q));
    }

    neg(P: PointOverFp): PointOverFp {
        if (this.is_zero(P)) return this.zero;

        return { x: this.Fp.mod(P.x), y: this.Fp.neg(P.y), z: P.z };
    }

    escalarMul(P: PointOverFp, k: bigint): PointOverFp {
        if (k === 0n) return this.zero;

        if (k < 0n) {
            k = -k;
            P = this.neg(P);
        }

        let R = P;
        let binary = k.toString(2);
        for (let i = 1; i < binary.length; i++) {
            R = this.add(R, R);
            if (binary[i] === "1") {
                R = this.add(R, P);
            }
        }

        return R;
    }
}

// /*
//     * Elliptic curve over Fq
//     * y² = x³ + a·x + b
//     * a, b are Fq elements
//     * 4·a³ + 27·b² != 0
//     * q is a prime power
//     */
export class EllipticCurveOverFq {
    readonly a: bigint[];
    readonly b: bigint[];
    readonly Fq: ExtensionField;

    constructor(a: bigint[], b: bigint[], field: ExtensionField) {
        const firstSummand = field.mul([4n], field.exp(a, 3n));
        const secondSummand = field.mul([27n], field.exp(b, 2n));
        const sum = field.add(firstSummand, secondSummand);
        if (field.eq(sum, field.zero)) {
            throw new Error("The curve is singular, choose another a and b");
        }

        // Compute the emebdding degree
        const k = 1;

        this.a = a;
        this.b = b;
        this.Fq = field;
    }

    // Public Accessors
    get zero(): null {
        return null;
    }

    // Comparators
    eq(P: PointOverFq, Q: PointOverFq): boolean {
        return this.Fq.eq(P.x,Q.x) && this.Fq.eq(P.y,Q.y) && this.Fq.eq(P.z, P.z);
    }

    neq(P: PointOverFq, Q: PointOverFq): boolean {
        return !this.eq(P, Q);
    }

    // Check if a point is the identity element
    is_zero(P: PointOverFq): boolean {
        return P === this.zero;
    }

    make_affine(P: PointOverFq) {
        let x_aff = this.Fq.div(P.x, this.Fq.mul(P.z, P.z))
        let y_aff = this.Fq.div(P.y, this.Fq.mul(this.Fq.mul(P.z, P.z), P.z))
        P.x = x_aff
        P.y = y_aff
        P.z = this.Fq.one
    }
    // Check that a point is on the curve
    is_on_curve(P: PointOverFq): boolean {
        this.make_affine(P)
        if (this.is_zero(P)) {
            return true;
        }

        const left_side = this.Fq.exp(P.y, 2n);
        const right_side = this.Fq.add(
            this.Fq.add(this.Fq.exp(P.x, 3n), this.Fq.mul(this.a, P.x)),
            this.b
        );

        return this.Fq.eq(left_side, right_side);
    }

    // Basic Arithmetic
    add(P: PointOverFq, Q: PointOverFq): PointOverFq {
        if (this.is_zero(P)) return Q;

        if (this.is_zero(Q)) return P;

        if (this.Fq.eq(P.x, Q.x)) {
            if (this.Fq.neq(P.y, Q.y)) {
                // P = -Q
                return this.zero;
            }
        }

        // let m: bigint[];
        // if (this.Fq.eq(P.x, Q.x) && this.Fq.eq(P.y, Q.y)) {
        //     m = this.Fq.div(
        //         this.Fq.add(this.Fq.mul([3n], this.Fq.mul(P.x, P.x)), this.a),
        //         this.Fq.mul([2n], P.y)
        //     );
        // } else {
        //     m = this.Fq.div(this.Fq.sub(Q.y, P.y), this.Fq.sub(Q.x, P.x));
        // }

        // const x = this.Fq.sub(this.Fq.sub(this.Fq.mul(m, m), P.x), Q.x);
        // const y = this.Fq.sub(this.Fq.mul(m, this.Fq.sub(P.x, x)), P.y);
        // return { x, y };

        if (this.eq(P, Q)) {
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
            let a = this.Fq.mul(P.x, P.x)
            let b = this.Fq.mul(P.y, P.y)
            let c = this.Fq.mul(b, b)
            let x1plusb = this.Fq.add(P.x, b)
            let x1plusbsq = this.Fq.mul(x1plusb, x1plusb)
            let d = this.Fq.mul([2n], this.Fq.sub(this.Fq.sub(x1plusbsq, a), b))
            let e = this.Fq.mul([3n], a)
            let f = this.Fq.mul(e, e)
            const x = this.Fq.sub(f, this.Fq.mul([2n], d))
            const y = this.Fq.sub(this.Fq.mul(e, this.Fq.sub(d, x)), this.Fq.mul([8n], c))
            const z = this.Fq.mul([2n], this.Fq.mul(P.y, P.z))
            return {x, y, z}
        } else {
            // https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
            let z1z1 = this.Fq.mul(P.z, P.z)
            let z2z2 = this.Fq.mul(Q.z, Q.z)
            let u1 = this.Fq.mul(P.x, z2z2)
            let u2 = this.Fq.mul(Q.x, z1z1)
            let s1 = this.Fq.mul(P.y, this.Fq.mul(Q.z, z2z2))
            let s2 = this.Fq.mul(Q.y, this.Fq.mul(P.z, z1z1))
            let h = this.Fq.sub(u2, u1)
            let hsq = this.Fq.mul([2n], h)
            let i = this.Fq.mul(hsq, hsq)
            let j = this.Fq.mul(h, i)
            let r = this.Fq.mul([2n], this.Fq.sub(s2, s1))
            let v = this.Fq.mul(u1, i)
            const x = this.Fq.sub(this.Fq.mul(r, r), this.Fq.sub(j, this.Fq.mul([2n], v)))
            const y = this.Fq.sub(this.Fq.mul(r, this.Fq.sub(v, x)), this.Fq.mul([2n], this.Fq.mul(s1, j)))
            let z1z2 = this.Fq.add(P.z, Q.z)
            let z1z2sq = this.Fq.mul(z1z2, z1z2)
            const z = this.Fq.mul(h, this.Fq.sub(this.Fq.sub(z1z2sq, z1z1), z2z2))
            return {x, y, z};
        }
    }

    sub(P: PointOverFq, Q: PointOverFq): PointOverFq {
        return this.add(P, this.neg(Q));
    }

    neg(P: PointOverFq): PointOverFq {
        if (this.is_zero(P)) return this.zero;

        return { x: this.Fq.mod(P.x), y: this.Fq.neg(P.y), z: P.z };
    }

    escalarMul(P: PointOverFq, k: bigint): PointOverFq {
        if (k === 0n) return this.zero;

        if (k < 0n) {
            k = -k;
            P = this.neg(P);
        }

        let R = P;
        let binary = k.toString(2);
        for (let i = 1; i < binary.length; i++) {
            R = this.add(R, R);
            if (binary[i] === "1") {
                R = this.add(R, P);
            }
        }

        return R;
    }
}

// /*
//     * Elliptic curve over Fq
//     * y² = x³ + a·x + b
//     * a, b are Fq elements
//     * 4·a³ + 27·b² != 0
//     * q is a prime power
//     */
export class EllipticCurveOverFqOverFq {
    readonly a: bigint[][];
    readonly b: bigint[][];
    readonly Fq: ExtensionFieldOverFq;

    constructor(a: bigint[][], b: bigint[][], field: ExtensionFieldOverFq) {
        const firstSummand = field.mul([[4n]], field.exp(a, 3n));
        const secondSummand = field.mul([[27n]], field.exp(b, 2n));
        const sum = field.add(firstSummand, secondSummand);
        if (field.eq(sum, field.zero)) {
            throw new Error("The curve is singular, choose another a and b");
        }

        // Compute the emebdding degree
        const k = 1;

        this.a = a;
        this.b = b;
        this.Fq = field;
    }

    // Public Accessors
    get zero(): null {
        return null;
    }

    // Comparators
    eq(P: PointOverFqOverFq, Q: PointOverFqOverFq): boolean {
        return this.Fq.eq(P.x,Q.x) && this.Fq.eq(P.y,Q.y) && this.Fq.eq(P.z, Q.z);
    }

    neq(P: PointOverFqOverFq, Q: PointOverFqOverFq): boolean {
        return !this.eq(P, Q);
    }

    // Check if a point is the identity element
    is_zero(P: PointOverFqOverFq): boolean {
        return P === this.zero;
    }

    make_affine(P: PointOverFqOverFq) {
        let x_aff = this.Fq.div(P.x, this.Fq.mul(P.z, P.z))
        let y_aff = this.Fq.div(P.y, this.Fq.mul(this.Fq.mul(P.z, P.z), P.z))
        P.x = x_aff
        P.y = y_aff
        P.z = this.Fq.one
    }
    // Check that a point is on the curve
    is_on_curve(P: PointOverFqOverFq): boolean {
        this.make_affine(P)
        if (this.is_zero(P)) {
            return true;
        }

        const left_side = this.Fq.exp(P.y, 2n);
        const right_side = this.Fq.add(
            this.Fq.add(this.Fq.exp(P.x, 3n), this.Fq.mul(this.a, P.x)),
            this.b
        );

        return this.Fq.eq(left_side, right_side);
    }

    // Basic Arithmetic
    add(P: PointOverFqOverFq, Q: PointOverFqOverFq): PointOverFqOverFq {
        if (this.is_zero(P)) return Q;

        if (this.is_zero(Q)) return P;

        if (this.Fq.eq(P.x, Q.x)) {
            if (this.Fq.neq(P.y, Q.y)) {
                // P = -Q
                return this.zero;
            }
        }

        // let m: bigint[][];
        // if (this.Fq.eq(P.x, Q.x) && this.Fq.eq(P.y, Q.y)) {
        //     m = this.Fq.div(
        //         this.Fq.add(this.Fq.mul([[3n]], this.Fq.mul(P.x, P.x)), this.a),
        //         this.Fq.mul([[2n]], P.y)
        //     );
        // } else {
        //     m = this.Fq.div(this.Fq.sub(Q.y, P.y), this.Fq.sub(Q.x, P.x));
        // }

        // const x = this.Fq.sub(this.Fq.sub(this.Fq.mul(m, m), P.x), Q.x);
        // const y = this.Fq.sub(this.Fq.mul(m, this.Fq.sub(P.x, x)), P.y);
        // return { x, y };

        if (this.eq(P, Q)) {
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
            let a = this.Fq.mul(P.x, P.x)
            let b = this.Fq.mul(P.y, P.y)
            let c = this.Fq.mul(b, b)
            let x1plusb = this.Fq.add(P.x, b)
            let x1plusbsq = this.Fq.mul(x1plusb, x1plusb)
            let d = this.Fq.mul([[2n]], this.Fq.sub(this.Fq.sub(x1plusbsq, a), b))
            let e = this.Fq.mul([[3n]], a)
            let f = this.Fq.mul(e, e)
            const x = this.Fq.sub(f, this.Fq.mul([[2n]], d))
            const y = this.Fq.sub(this.Fq.mul(e, this.Fq.sub(d, x)), this.Fq.mul([[8n]], c))
            const z = this.Fq.mul([[2n]], this.Fq.mul(P.y, P.z))
            return {x, y, z}
        } else {
            // https://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
            let z1z1 = this.Fq.mul(P.z, P.z)
            let z2z2 = this.Fq.mul(Q.z, Q.z)
            let u1 = this.Fq.mul(P.x, z2z2)
            let u2 = this.Fq.mul(Q.x, z1z1)
            let s1 = this.Fq.mul(P.y, this.Fq.mul(Q.z, z2z2))
            let s2 = this.Fq.mul(Q.y, this.Fq.mul(P.z, z1z1))
            let h = this.Fq.sub(u2, u1)
            let hsq = this.Fq.mul([[2n]], h)
            let i = this.Fq.mul(hsq, hsq)
            let j = this.Fq.mul(h, i)
            let r = this.Fq.mul([[2n]], this.Fq.sub(s2, s1))
            let v = this.Fq.mul(u1, i)
            const x = this.Fq.sub(this.Fq.mul(r, r), this.Fq.sub(j, this.Fq.mul([[2n]], v)))
            const y = this.Fq.sub(this.Fq.mul(r, this.Fq.sub(v, x)), this.Fq.mul([[2n]], this.Fq.mul(s1, j)))
            let z1z2 = this.Fq.add(P.z, Q.z)
            let z1z2sq = this.Fq.mul(z1z2, z1z2)
            const z = this.Fq.mul(h, this.Fq.sub(this.Fq.sub(z1z2sq, z1z1), z2z2))
            return {x, y, z};
        }        
    }

    sub(P: PointOverFqOverFq, Q: PointOverFqOverFq): PointOverFqOverFq {
        return this.add(P, this.neg(Q));
    }

    neg(P: PointOverFqOverFq): PointOverFqOverFq {
        if (this.is_zero(P)) return this.zero;

        return { x: this.Fq.mod(P.x), y: this.Fq.neg(P.y), z: P.z };
    }

    escalarMul(P: PointOverFqOverFq, k: bigint): PointOverFqOverFq {
        if (k === 0n) return this.zero;

        if (k < 0n) {
            k = -k;
            P = this.neg(P);
        }

        let R = P;
        let binary = k.toString(2);
        for (let i = 1; i < binary.length; i++) {
            R = this.add(R, R);
            if (binary[i] === "1") {
                R = this.add(R, P);
            }
        }

        return R;
    }
}

export function embedding_degree(Fp: PrimeField, r: bigint): bigint {
    let k = 1n;
    while ((Fp.p ** k - 1n) % r !== 0n) {
        k += 1n;
    }

    return k;
}

// Tests
// const Fp = new PrimeField(11n);
// const E = new EllipticCurveOverFp(0n, 4n, Fp);
// const r = 3n;
// const k = E.embedding_degree(r);
// console.log(k);

// const Fp = new PrimeField(11n);
// const E = new EllipticCurveOverFp(7n, 2n, Fp);
// const r = 7n;
// const k = E.embedding_degree(r);
// console.log(k);

// export class EllipticCurve<T extends FiniteField<U>, U> {
//     readonly a: bigint;
//     readonly b: bigint;
//     readonly F: PrimeField;

//     constructor(a: bigint, b: bigint, field: PrimeField) {
//         const four = field instanceof PrimeField ? 4n : [4n];
//         const ts = field instanceof PrimeField ? 27n : [27n];
//         const firstSummand = field.mul(four as U, field.exp(a, 3n));
//         const secondSummand = field.mul(ts as U, field.exp(b, 2n));
//         const sum = field.add(firstSummand, secondSummand);
//         if (field.eq(sum, field.zero)) {
//             throw new Error("The curve is singular, choose another a and b");
//         }

//         this.a = a;
//         this.b = b;
//         this.F = field;
//     }

//     // Public Accessors
//     get zero(): null {
//         return null;
//     }

//     // Check if a Point is the identity element
//     is_zero(P: PointOverFp): boolean {
//         return P === this.zero;
//     }

//     // Check that a point is on the curve defined by y² == x³ + a·x + b
//     is_on_curve(P: PointOverFp): boolean {
//         if (this.is_zero(P)) {
//             return true;
//         }

//         const left_side = this.F.exp(P.y, 2n);
//         const right_side = this.F.add(
//             this.F.add(this.F.exp(P.x, 3n), this.F.mul(this.a, P.x)),
//             this.b
//         );

//         return this.F.eq(left_side, right_side);
//     }

//     // Basic Arithmetic
//     add(P: PointOverFp, Q: PointOverFp): PointOverFp {
//         if (this.is_zero(P)) return Q;

//         if (this.is_zero(Q)) return P;

//         if (P.x === Q.x) {
//             if (P.y !== Q.y) {
//                 // P = -Q
//                 return this.zero;
//             }
//         }

//         let m: bigint;
//         const three = this.F instanceof PrimeField ? 3n : [3n];
//         const two = this.F instanceof PrimeField ? 2n : [2n];
//         if (P.x === Q.x && P.y === Q.y) {
//             m = this.F.div(
//                 this.F.add(this.F.mul(three as U, this.F.mul(P.x, P.x)), this.a),
//                 this.F.mul(two as U, P.y)
//             );
//         } else {
//             m = this.F.div(this.F.sub(Q.y, P.y), this.F.sub(Q.x, P.x));
//         }

//         const x = this.F.sub(this.F.sub(this.F.mul(m, m), P.x), Q.x);
//         const y = this.F.sub(this.F.mul(m, this.F.sub(P.x, x)), P.y);
//         return { x, y };
//     }

//     sub(P: PointOverFp, Q: PointOverFp): PointOverFp {
//         return this.add(P, this.neg(Q));
//     }

//     neg(P: PointOverFp): PointOverFp {
//         if (this.is_zero(P)) return this.zero;

//         return { x: PrimeFieldhis.F.mod(P.x), y: PrimeFieldhis.F.neg(P.y) };
//     }

//     escalarMul(P: PointOverFp, k: bigint): PointOverFp {
//         if (k === 0n) return this.zero;

//         if (k < 0n) {
//             k = -k;
//             P = this.neg(P);
//         }

//         let R = P;
//         let binary = k.toString(2);
//         for (let i = 1; i < binary.length; i++) {
//             R = this.add(R, R);
//             if (binary[i] === "1") {
//                 R = this.add(R, P);
//             }
//         }

//         return R;
//     }

//     embedding_degree(): number {
//         let k = 1
//         while (this.F.exp(this.F.p, k) !== this.F.one) {
//             k += 1
//         }

//         return k;
//     }

//     // Fix this
//     // twist(P: PointFq, w2: bigint[], w3: bigint[]): PointFq {
//     //     if (this.is_zero(P)) return this.zero;

//     //     // Field isomorphism from Fp[X]/(X²) to Fp[X]/(X² - 18·X + 82)
//     //     let xcoeffs = [
//     //         this.F.Fp.sub(P.x[0], this.F.Fp.mul(9n, P.x[1])),
//     //         P.x[1],
//     //     ];
//     //     let ycoeffs = [
//     //         this.F.Fp.sub(P.y[0], this.F.Fp.mul(9n, P.y[1])),
//     //         P.y[1],
//     //     ];
//     //     // Isomorphism into subfield of Fp[X]/(w¹² - 18·w⁶ + 82),
//     //     // where w⁶ = X
//     //     let nx = [xcoeffs[0], 0n, 0n, 0n, 0n, 0n, xcoeffs[1]];
//     //     let ny = [ycoeffs[0], 0n, 0n, 0n, 0n, 0n, ycoeffs[1]];

//     //     // Divide x coord by w² and y coord by w³
//     //     let x = this.F.div(nx, w2);
//     //     let y = this.F.div(ny, w3);

//     //     return { x, y };
//     // }
// }
