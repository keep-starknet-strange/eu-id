//! One SHA-256 compression block as a layered quadratic boolean circuit.
//!
//! Every wire is a single bit. Gates are binary and quadratic:
//!   AND(a,b), XOR(a,b), and unary NOT(a) (affine, folded into XOR-with-1).
//! Modular 32-bit additions are expanded to explicit ripple-carry bit gates,
//! so the ENTIRE compression block is a boolean DAG of quadratic gates — no
//! opaque arithmetic. This is the gate population whose sumcheck we price.
//!
//! Layering: gates are topologically leveled by longest-path depth from the
//! inputs. Layer L's gates read only wires produced at depth < L. This is the
//! standard GKR layering; the per-layer gate count × sumcheck rounds gives the
//! term count we measure.

pub const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

pub const IV: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    /// Input wire (constant or block input); value carried in `Circuit::inputs`.
    Input,
    And(usize, usize),
    Xor(usize, usize),
    /// NOT(a) == XOR(a, const-1). Affine; still degree-1 so quadratic-safe.
    Not(usize),
}

pub struct Circuit {
    pub gates: Vec<Op>,
    /// depth[i] = layer index of gate i (0 for inputs).
    pub depth: Vec<u32>,
    pub n_layers: u32,
    pub inputs: Vec<bool>, // concrete assignment of the Input gates (by gate id order)
    /// Wire ids of the 8 output words (256 bits), LSB-first per word.
    pub out_wires: [[usize; 32]; 8],
}

struct Builder {
    gates: Vec<Op>,
    depth: Vec<u32>,
    input_vals: Vec<bool>,
    const0: usize,
    const1: usize,
}

impl Builder {
    fn new() -> Self {
        let mut b = Builder {
            gates: Vec::new(),
            depth: Vec::new(),
            input_vals: Vec::new(),
            const0: 0,
            const1: 0,
        };
        b.const0 = b.push_input(false);
        b.const1 = b.push_input(true);
        b
    }
    fn push_input(&mut self, v: bool) -> usize {
        let id = self.gates.len();
        self.gates.push(Op::Input);
        self.depth.push(0);
        self.input_vals.push(v);
        id
    }
    fn and(&mut self, a: usize, b: usize) -> usize {
        let d = self.depth[a].max(self.depth[b]) + 1;
        let id = self.gates.len();
        self.gates.push(Op::And(a, b));
        self.depth.push(d);
        id
    }
    fn xor(&mut self, a: usize, b: usize) -> usize {
        let d = self.depth[a].max(self.depth[b]) + 1;
        let id = self.gates.len();
        self.gates.push(Op::Xor(a, b));
        self.depth.push(d);
        id
    }
    fn not(&mut self, a: usize) -> usize {
        let d = self.depth[a] + 1;
        let id = self.gates.len();
        self.gates.push(Op::Not(a));
        self.depth.push(d);
        id
    }
    fn xor3(&mut self, a: usize, b: usize, c: usize) -> usize {
        let t = self.xor(a, b);
        self.xor(t, c)
    }
}

/// 32-bit word as 32 wire ids, index 0 = LSB.
type Word = [usize; 32];

fn rotr(w: &Word, n: usize) -> Word {
    let mut o = [0usize; 32];
    for i in 0..32 {
        o[i] = w[(i + n) % 32];
    }
    o
}
fn shr(b: &mut Builder, w: &Word, n: usize) -> Word {
    let mut o = [b.const0; 32];
    for i in 0..(32 - n) {
        o[i] = w[i + n];
    }
    o
}

fn xor_word(b: &mut Builder, x: &Word, y: &Word) -> Word {
    let mut o = [0usize; 32];
    for i in 0..32 {
        o[i] = b.xor(x[i], y[i]);
    }
    o
}

/// Ripple-carry 32-bit adder (mod 2^32). Full-adder per bit:
///   sum = a ^ b ^ cin ; cout = (a&b) | (cin&(a^b))
/// OR expressed with XOR/AND: a|b = a ^ b ^ (a&b). We build carry as
///   cout = (a&b) ^ (cin & (a^b))  [the two AND terms are disjoint here since
///   if a&b then a^b=0, so no double count] — valid boolean identity.
fn add_word(b: &mut Builder, x: &Word, y: &Word) -> Word {
    let mut out = [0usize; 32];
    let mut carry = b.const0;
    for i in 0..32 {
        let axorb = b.xor(x[i], y[i]);
        let sum = b.xor(axorb, carry);
        out[i] = sum;
        if i < 31 {
            let ab = b.and(x[i], y[i]);
            let cx = b.and(carry, axorb);
            carry = b.xor(ab, cx);
        }
    }
    out
}

fn ch(b: &mut Builder, e: &Word, f: &Word, g: &Word) -> Word {
    // (e&f) ^ (~e & g)
    let mut o = [0usize; 32];
    for i in 0..32 {
        let ef = b.and(e[i], f[i]);
        let ne = b.not(e[i]);
        let neg = b.and(ne, g[i]);
        o[i] = b.xor(ef, neg);
    }
    o
}

fn maj(b: &mut Builder, x: &Word, y: &Word, z: &Word) -> Word {
    // (x&y) ^ (x&z) ^ (y&z)
    let mut o = [0usize; 32];
    for i in 0..32 {
        let xy = b.and(x[i], y[i]);
        let xz = b.and(x[i], z[i]);
        let yz = b.and(y[i], z[i]);
        o[i] = b.xor3(xy, xz, yz);
    }
    o
}

fn big_sigma0(b: &mut Builder, x: &Word) -> Word {
    let a = rotr(x, 2);
    let c = rotr(x, 13);
    let d = rotr(x, 22);
    let mut o = [0usize; 32];
    for i in 0..32 {
        o[i] = b.xor3(a[i], c[i], d[i]);
    }
    o
}
fn big_sigma1(b: &mut Builder, x: &Word) -> Word {
    let a = rotr(x, 6);
    let c = rotr(x, 11);
    let d = rotr(x, 25);
    let mut o = [0usize; 32];
    for i in 0..32 {
        o[i] = b.xor3(a[i], c[i], d[i]);
    }
    o
}
fn small_sigma0(b: &mut Builder, x: &Word) -> Word {
    let r7 = rotr(x, 7);
    let r18 = rotr(x, 18);
    let s3 = shr(b, x, 3);
    let mut o = [0usize; 32];
    for i in 0..32 {
        o[i] = b.xor3(r7[i], r18[i], s3[i]);
    }
    o
}
fn small_sigma1(b: &mut Builder, x: &Word) -> Word {
    let r17 = rotr(x, 17);
    let r19 = rotr(x, 19);
    let s10 = shr(b, x, 10);
    let mut o = [0usize; 32];
    for i in 0..32 {
        o[i] = b.xor3(r17[i], r19[i], s10[i]);
    }
    o
}

fn const_word(b: &mut Builder, v: u32) -> Word {
    let mut o = [0usize; 32];
    for i in 0..32 {
        o[i] = if (v >> i) & 1 == 1 { b.const1 } else { b.const0 };
    }
    o
}

/// Build the full 64-round compression for one block.
/// Inputs: the 8 IV words (as input wires) and 16 message words (input wires).
pub fn build_compression_block(msg: &[u32; 16]) -> Circuit {
    let mut b = Builder::new();

    // Input words: 8 state (IV) + 16 message. Real values baked in so the
    // circuit evaluates a genuine compression (correctness assert uses these).
    let mut state: [Word; 8] = std::array::from_fn(|_| [0usize; 32]);
    for (s, &iv) in state.iter_mut().zip(IV.iter()) {
        let mut w = [0usize; 32];
        for i in 0..32 {
            w[i] = b.push_input((iv >> i) & 1 == 1);
        }
        *s = w;
    }
    // Message schedule W[0..64]. W[0..16] are inputs; rest computed.
    let mut w: Vec<Word> = Vec::with_capacity(64);
    for t in 0..16 {
        let mut wd = [0usize; 32];
        for i in 0..32 {
            wd[i] = b.push_input((msg[t] >> i) & 1 == 1);
        }
        w.push(wd);
    }
    for t in 16..64 {
        let s1 = small_sigma1(&mut b, &w[t - 2]);
        let s0 = small_sigma0(&mut b, &w[t - 15]);
        let a1 = add_word(&mut b, &w[t - 16], &s0);
        let a2 = add_word(&mut b, &a1, &w[t - 7]);
        let a3 = add_word(&mut b, &a2, &s1);
        w.push(a3);
    }

    let mut a = state[0];
    let mut bb = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    for t in 0..64 {
        let kw = const_word(&mut b, K[t]);
        let s1 = big_sigma1(&mut b, &e);
        let chv = ch(&mut b, &e, &f, &g);
        // T1 = h + Σ1(e) + Ch + K + W[t]
        let t1a = add_word(&mut b, &h, &s1);
        let t1b = add_word(&mut b, &t1a, &chv);
        let t1c = add_word(&mut b, &t1b, &kw);
        let t1 = add_word(&mut b, &t1c, &w[t]);
        let s0 = big_sigma0(&mut b, &a);
        let majv = maj(&mut b, &a, &bb, &c);
        let t2 = add_word(&mut b, &s0, &majv);

        h = g;
        g = f;
        f = e;
        e = add_word(&mut b, &d, &t1);
        d = c;
        c = bb;
        bb = a;
        a = add_word(&mut b, &t1, &t2);
    }

    // Final add: H_out = IV + working (mod 2^32). Produces the 8 output words.
    let _ = xor_word; // (kept available; not needed since add covers it)
    let outs = [a, bb, c, d, e, f, g, h];
    let mut out_wires = [[0usize; 32]; 8];
    for (w, (o, iv_w)) in outs.iter().zip(state.iter()).enumerate() {
        out_wires[w] = add_word(&mut b, o, iv_w);
    }

    let n_layers = *b.depth.iter().max().unwrap() + 1;
    Circuit {
        gates: b.gates,
        depth: b.depth,
        n_layers,
        inputs: b.input_vals,
        out_wires,
    }
}

/// Reference native SHA-256 single-block compression (for the correctness
/// assert): compress the given message into the IV.
pub fn native_compress(msg: &[u32; 16]) -> [u32; 8] {
    let mut w = [0u32; 64];
    w[..16].copy_from_slice(msg);
    for t in 16..64 {
        let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
        let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
        w[t] = w[t - 16]
            .wrapping_add(s0)
            .wrapping_add(w[t - 7])
            .wrapping_add(s1);
    }
    let mut v = IV;
    let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) =
        (v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
    for t in 0..64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let chv = (e & f) ^ ((!e) & g);
        let t1 = h
            .wrapping_add(s1)
            .wrapping_add(chv)
            .wrapping_add(K[t])
            .wrapping_add(w[t]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let majv = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(majv);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    v[0] = v[0].wrapping_add(a);
    v[1] = v[1].wrapping_add(b);
    v[2] = v[2].wrapping_add(c);
    v[3] = v[3].wrapping_add(d);
    v[4] = v[4].wrapping_add(e);
    v[5] = v[5].wrapping_add(f);
    v[6] = v[6].wrapping_add(g);
    v[7] = v[7].wrapping_add(h);
    v
}

/// Evaluate the boolean circuit natively; returns per-gate bit values.
pub fn eval_bits(c: &Circuit) -> Vec<bool> {
    let mut v = vec![false; c.gates.len()];
    let mut ii = 0usize;
    for (i, g) in c.gates.iter().enumerate() {
        v[i] = match *g {
            Op::Input => {
                let x = c.inputs[ii];
                ii += 1;
                x
            }
            Op::And(a, b) => v[a] & v[b],
            Op::Xor(a, b) => v[a] ^ v[b],
            Op::Not(a) => !v[a],
        };
    }
    v
}
