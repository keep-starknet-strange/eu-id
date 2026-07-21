//! Merkle node hash decision gate: SIMD-16 Blake2s (the incumbent stwo Merkle
//! hasher) vs hardware SHA-256 on ARMv8 crypto extensions.
//!
//! The question this answers: if we swap stwo's Merkle tree hasher from Blake2s
//! to SHA-256 to exploit ARMv8 HW SHA-256 (phones have HW SHA-256, no HW
//! Blake2s), does SHA-256 clearly beat the SIMD-16 Blake2s per Merkle node?
//! One node = two 32-byte children -> one 32-byte digest (64-byte input).
//!
//! Workload for every case: hash one layer of N = 2^20 Merkle nodes,
//! single-threaded. All cases hash byte-identical content.
//!
//! Run (fat-LTO release), pinned to a big core if the OS allows it:
//!   cargo run --release --example merkle_hash_bench
//! On macOS you cannot hard-pin to a P-core, but `taskpolicy -c utility` is the
//! wrong direction; just run on an otherwise-idle machine. On Linux:
//!   taskset -c 0 cargo run --release --example merkle_hash_bench
//!
//! NOTE on the SHA-256 block asymmetry that is part of the decision:
//! a 64-byte message needs SHA-256 padding (0x80 + length) that overflows into a
//! SECOND 512-bit block, so standard SHA-256 over a Merkle node costs TWO
//! compressions. Blake2s does it in ONE. We bench the honest 2-block SHA-256 AND
//! a Merkle-specialized 1-block variant (raw 64-byte block, no length padding —
//! a construction many tree hashers use; it deviates from standard SHA-256 and
//! would need its own security note) so both numbers are on the table.

use std::hint::black_box;
use std::time::{Duration, Instant};

use sha2::{Digest, Sha256};
use stwo::core::vcs::blake2_hash::Blake2sHash;
use stwo::core::vcs::blake2_merkle::Blake2sMerkleHasher;
use stwo::prover::backend::simd::column::BaseColumn;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::vcs::ops::MerkleOps;

const LOG_N: u32 = 20;
const N: usize = 1 << LOG_N; // 2^20 Merkle nodes per layer.

/// Runs `f` (which processes `nodes_per_call` nodes) repeatedly for ~1s and
/// returns (ns_per_node, mnodes_per_s). `f` must black_box its output so the
/// optimizer cannot delete the work.
fn bench<F: FnMut()>(nodes_per_call: usize, mut f: F) -> (f64, f64) {
    f(); // warmup / prime caches
    let mut iters: u64 = 0;
    let start = Instant::now();
    loop {
        f();
        iters += 1;
        if start.elapsed() >= Duration::from_secs(1) {
            break;
        }
    }
    let secs = start.elapsed().as_secs_f64();
    let total_nodes = iters as f64 * nodes_per_call as f64;
    (secs * 1e9 / total_nodes, total_nodes / secs / 1e6)
}

// ---------------------------------------------------------------------------
// Raw ARMv8 SHA-256 via core::arch::aarch64 crypto-extension intrinsics.
// 4 independent nodes are interleaved (loops over `l in 0..4` inside each round
// group unroll into 4 independent instruction streams) to hide the ~multi-cycle
// latency of vsha256hq/vsha256h2q — the realistic custom-hasher ceiling.
// ---------------------------------------------------------------------------
#[cfg(target_arch = "aarch64")]
mod arm_sha {
    use core::arch::aarch64::*;

    const H: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];

    /// Compress one 512-bit block (given as 4 loaded+byte-reversed message
    /// vectors) into the running (abef, cdgh) state pair for one lane.
    #[target_feature(enable = "neon,sha2")]
    #[inline]
    unsafe fn block(
        s0: uint32x4_t,
        s1: uint32x4_t,
        m: &[u8; 64],
        kv: &[uint32x4_t; 16],
    ) -> (uint32x4_t, uint32x4_t) {
        // Load 16 message words as 4 vectors, byte-reverse to big-endian.
        let mut w = [vdupq_n_u32(0); 16];
        for (j, wj) in w.iter_mut().take(4).enumerate() {
            let v = vld1q_u32(m.as_ptr().add(j * 16) as *const u32);
            *wj = vreinterpretq_u32_u8(vrev32q_u8(vreinterpretq_u8_u32(v)));
        }
        // Message schedule: w[j] = su1(su0(w[j-4],w[j-3]), w[j-2], w[j-1]).
        for j in 4..16 {
            let t = vsha256su0q_u32(w[j - 4], w[j - 3]);
            w[j] = vsha256su1q_u32(t, w[j - 2], w[j - 1]);
        }
        // 16 round-groups of 4 rounds each = 64 rounds.
        let (mut a, mut b) = (s0, s1);
        for j in 0..16 {
            let tmp = vaddq_u32(w[j], kv[j]);
            let t2 = a;
            a = vsha256hq_u32(a, b, tmp);
            b = vsha256h2q_u32(b, t2, tmp);
        }
        (vaddq_u32(a, s0), vaddq_u32(b, s1))
    }

    #[inline]
    unsafe fn digest_bytes(s0: uint32x4_t, s1: uint32x4_t) -> [u8; 32] {
        let mut words = [0u32; 8];
        vst1q_u32(words.as_mut_ptr(), s0);
        vst1q_u32(words.as_mut_ptr().add(4), s1);
        let mut out = [0u8; 32];
        for i in 0..8 {
            out[i * 4..i * 4 + 4].copy_from_slice(&words[i].to_be_bytes());
        }
        out
    }

    #[inline]
    fn kv() -> [uint32x4_t; 16] {
        unsafe { std::array::from_fn(|j| vld1q_u32(K.as_ptr().add(j * 4))) }
    }

    /// SHA-256 padding second block for a fixed 64-byte message:
    /// 0x80, zeros, then the 64-bit big-endian bit length (64*8 = 512).
    fn pad_block() -> [u8; 64] {
        let mut p = [0u8; 64];
        p[0] = 0x80;
        p[56..64].copy_from_slice(&(512u64).to_be_bytes());
        p
    }

    /// Standard SHA-256 of one 64-byte node: 2 compression blocks. 4-way.
    #[target_feature(enable = "neon,sha2")]
    unsafe fn sha256_2block_x4(nodes: &[[u8; 64]; 4], kv: &[uint32x4_t; 16]) -> [[u8; 32]; 4] {
        let pad = pad_block();
        let h0 = vld1q_u32(H.as_ptr());
        let h1 = vld1q_u32(H.as_ptr().add(4));
        let mut s0 = [h0; 4];
        let mut s1 = [h1; 4];
        // Block 0 (the node), all 4 lanes interleaved.
        for l in 0..4 {
            let (a, b) = block(s0[l], s1[l], &nodes[l], kv);
            s0[l] = a;
            s1[l] = b;
        }
        // Block 1 (padding), all 4 lanes interleaved.
        for l in 0..4 {
            let (a, b) = block(s0[l], s1[l], &pad, kv);
            s0[l] = a;
            s1[l] = b;
        }
        std::array::from_fn(|l| digest_bytes(s0[l], s1[l]))
    }

    /// Merkle-specialized 1-block variant: compress the 64-byte node as a single
    /// block with no length padding. NOT standard SHA-256 (needs a security
    /// note); it is the cheapest a SHA-256-based fixed-64B tree hasher can be.
    #[target_feature(enable = "neon,sha2")]
    unsafe fn sha256_1block_x4(nodes: &[[u8; 64]; 4], kv: &[uint32x4_t; 16]) -> [[u8; 32]; 4] {
        let h0 = vld1q_u32(H.as_ptr());
        let h1 = vld1q_u32(H.as_ptr().add(4));
        let mut s0 = [h0; 4];
        let mut s1 = [h1; 4];
        for l in 0..4 {
            let (a, b) = block(s0[l], s1[l], &nodes[l], kv);
            s0[l] = a;
            s1[l] = b;
        }
        std::array::from_fn(|l| digest_bytes(s0[l], s1[l]))
    }

    /// Public entry: SHA-256 (2-block, standard) over a lane of 4 nodes.
    pub fn digest_2block_x4(nodes: &[[u8; 64]; 4]) -> [[u8; 32]; 4] {
        unsafe { sha256_2block_x4(nodes, &kv()) }
    }

    /// Public entry: 1-block Merkle-specialized variant over a lane of 4 nodes.
    pub fn digest_1block_x4(nodes: &[[u8; 64]; 4]) -> [[u8; 32]; 4] {
        unsafe { sha256_1block_x4(nodes, &kv()) }
    }
}

/// Build one layer: `n` random 64-byte nodes and the matching Blake2s previous
/// layer of `2n` child hashes (node i's two 32-byte halves).
fn build_layer(n: usize) -> (Vec<[u8; 64]>, Vec<Blake2sHash>) {
    let mut nodes = vec![[0u8; 64]; n];
    // Cheap deterministic fill (xorshift-ish) — content is irrelevant to timing.
    let mut x: u64 = 0x9e3779b97f4a7c15;
    for node in nodes.iter_mut() {
        for b in node.iter_mut() {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *b = x as u8;
        }
    }
    let mut prev = Vec::with_capacity(2 * n);
    for node in &nodes {
        let mut c0 = [0u8; 32];
        let mut c1 = [0u8; 32];
        c0.copy_from_slice(&node[0..32]);
        c1.copy_from_slice(&node[32..64]);
        prev.push(Blake2sHash(c0));
        prev.push(Blake2sHash(c1));
    }
    (nodes, prev)
}

fn main() {
    let arch = std::env::consts::ARCH;
    let hw = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(0);
    eprintln!("target_arch = {arch}, available_parallelism hint = {hw}, single-threaded bench");
    eprintln!("workload: 1 layer of N = 2^{LOG_N} = {N} Merkle nodes (64B -> 32B) per case\n");

    let (nodes, prev) = build_layer(N);

    // --- Case 1: incumbent SIMD-16 Blake2s via the real stwo Merkle path. -----
    // Driving the actual MerkleOps::commit_on_layer (no columns, prev_layer =
    // the 2^21 child hashes) — this is exactly what the prover does and includes
    // the transpose/packing overhead, which is fair (it is what we'd replace).
    let no_cols: [&BaseColumn; 0] = [];
    let (blake_ns, blake_mn) = bench(N, || {
        let layer = <SimdBackend as MerkleOps<Blake2sMerkleHasher>>::commit_on_layer(
            LOG_N,
            Some(black_box(&prev)),
            &no_cols,
        );
        black_box(layer[0].0[0]);
    });
    println!("blake2s_simd16      : {blake_ns:7.2} ns/node   {blake_mn:8.2} Mnodes/s");

    // --- Case 2: sha2 crate single-stream (auto HW via cpufeatures on aarch64).
    let (sha2c_ns, sha2c_mn) = bench(N, || {
        let mut acc = 0u8;
        for node in &nodes {
            let d = Sha256::digest(node);
            acc ^= d[0];
        }
        black_box(acc);
    });
    println!("sha2_crate_1stream  : {sha2c_ns:7.2} ns/node   {sha2c_mn:8.2} Mnodes/s  (>1GB/s => HW)");
    // sha2 crate throughput sanity: 64 B/node.
    let sha2c_gbs = sha2c_mn * 1e6 * 64.0 / 1e9;
    let sha2c_hw = sha2c_gbs > 1.0;
    eprintln!(
        "  sha2 crate: {sha2c_gbs:.2} GB/s of message => HW SHA-256 {}",
        if sha2c_hw { "ENGAGED" } else { "NOT detected" }
    );

    // --- Cases 3a/3b: raw ARMv8 intrinsics, 4-way interleaved. ----------------
    #[cfg(target_arch = "aarch64")]
    let (sha2b_ns, sha2b_mn, sha1b_ns, sha1b_mn) = {
        // Correctness: 2-block intrinsic must equal sha2 crate (standard SHA-256).
        for chunk in nodes.chunks_exact(4).take(4) {
            let arr: [[u8; 64]; 4] = [chunk[0], chunk[1], chunk[2], chunk[3]];
            let got = arm_sha::digest_2block_x4(&arr);
            for l in 0..4 {
                let want = Sha256::digest(arr[l]);
                assert_eq!(
                    &got[l][..],
                    &want[..],
                    "ARM intrinsics 2-block != sha2 crate (lane {l})"
                );
            }
        }
        eprintln!("  ARM intrinsics 2-block output verified == sha2 crate\n");

        let n4 = N / 4;
        let (b2_ns, b2_mn) = bench(N, || {
            let mut acc = 0u8;
            for chunk in nodes.chunks_exact(4) {
                let arr: [[u8; 64]; 4] = [chunk[0], chunk[1], chunk[2], chunk[3]];
                let d = arm_sha::digest_2block_x4(&arr);
                acc ^= d[0][0];
            }
            black_box((acc, n4));
        });
        let (b1_ns, b1_mn) = bench(N, || {
            let mut acc = 0u8;
            for chunk in nodes.chunks_exact(4) {
                let arr: [[u8; 64]; 4] = [chunk[0], chunk[1], chunk[2], chunk[3]];
                let d = arm_sha::digest_1block_x4(&arr);
                acc ^= d[0][0];
            }
            black_box(acc);
        });
        (b2_ns, b2_mn, b1_ns, b1_mn)
    };
    #[cfg(not(target_arch = "aarch64"))]
    let (sha2b_ns, sha2b_mn, sha1b_ns, sha1b_mn) = {
        println!("sha256_arm_2block_x4: n/a (not aarch64)");
        println!("sha256_arm_1block_x4: n/a (not aarch64)");
        (f64::NAN, f64::NAN, f64::NAN, f64::NAN)
    };
    #[cfg(target_arch = "aarch64")]
    {
        println!("sha256_arm_2block_x4: {sha2b_ns:7.2} ns/node   {sha2b_mn:8.2} Mnodes/s  (honest standard SHA-256)");
        println!("sha256_arm_1block_x4: {sha1b_ns:7.2} ns/node   {sha1b_mn:8.2} Mnodes/s  (Merkle-specialized, non-standard)");
    }

    // best SHA number (lower ns/node is better) across the SHA cases.
    let sha_candidates = [sha2c_ns, sha2b_ns, sha1b_ns];
    let best_sha = sha_candidates
        .iter()
        .cloned()
        .filter(|v| v.is_finite())
        .fold(f64::INFINITY, f64::min);
    let ratio = blake_ns / best_sha;
    println!(
        "\nblake2s / best_sha = {ratio:.3}  ({} on this workload)",
        if ratio > 1.0 { "SHA wins" } else { "Blake2s wins" }
    );

    // --- Machine-readable summary ---------------------------------------------
    println!(
        "JSON {{\"blake2s_simd16\":[{blake_ns:.2},{blake_mn:.2}],\
\"sha2_crate_1stream\":[{sha2c_ns:.2},{sha2c_mn:.2}],\
\"sha256_arm_2block_x4\":[{sha2b_ns:.2},{sha2b_mn:.2}],\
\"sha256_arm_1block_x4\":[{sha1b_ns:.2},{sha1b_mn:.2}],\
\"sha2_crate_hw\":{sha2c_hw},\"blake2s_ns_over_best_sha_ns\":{ratio:.3}}}"
    );
}
