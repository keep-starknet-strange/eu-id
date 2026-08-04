//! Measures Merkle hash performance without production changes.
//!
//! Replays the hash-node pattern from the two mdoc proof Merkle trees.
//! It preserves invocation counts and input byte volumes.
//! The benchmark measures three hashers:
//!   - Blake2s  (current, used by both stwo `Blake2sMerkleHasher` and the
//!     coprocessor `merkle.rs`)
//!   - Blake3   (`blake3` crate)
//!   - SHA-256 (`sha2` crate).
//! On AArch64, SHA-256 uses the ARMv8 SHA extensions.
//! The throughput check requires at least 1.5 GB/s on one thread.
//!
//! This kernel replay does not run Stwo.
//! Each hash invocation receives an input buffer with the measured byte length.
//! Stwo inputs contain child hashes and M31 column words.
//! Coprocessor inputs contain domain data, indices, lengths, and field limbs.
//! This method isolates hash-kernel cost.
//! It excludes memory layout and SIMD packing effects.
//!
//! Run:  RAYON_NUM_THREADS=1 cargo test -p eu-id-ec-coprocessor --release \
//!         --test hasher_bakeoff -- --ignored --nocapture

use std::time::{Duration, Instant};

use blake2::{Blake2s256, Digest};
use sha2::Sha256;

// STARK uses `committed_log = base_log + 2`.
// The layouts map each base log to its column count.
// Preprocessed: {16: 33, 4: 3}.
// Trace: {16: 9, 4: 3}.
// Interaction: {16: 20, 4: 8}.
// At committed depth d, the Stwo tree has 2^d nodes.
// A non-root node hashes two 32-byte child hashes.
// It also hashes one M31 word for each column with committed log d.
const LOG_BLOWUP: u32 = 2;
const STARK_TREES: &[&[(u32, usize)]] = &[
    &[(16, 33), (4, 3)], // preprocessed
    &[(16, 9), (4, 3)],  // trace
    &[(16, 20), (4, 8)], // interaction
];
const HASH_BYTES: usize = 32; // Blake2s / SHA-256 / Blake3 all 32-byte digests here.
const CHILD_BYTES: usize = 2 * HASH_BYTES; // 64
const M31_BYTES: usize = 4;

// The Ligero v4 tree includes the claim-blind kernel check.
// It transposes `committed_rows` codewords into one leaf for each column.
// Each leaf hashes one field limb for each committed row and a 39-byte prefix.
// Internal nodes hash a 23-byte domain prefix and two child hashes.
const COPROC_CODEWORD_LEN: usize = 4096;
const COPROC_COMMITTED_ROWS: usize = 220; // prior probe + the kernel-check mask row
const COPROC_FIELD_BYTES: usize = 32;
const COPROC_LEAF_PREFIX: usize = 23 + 8 + 8; // "eu-id-s4-ligero-leaf-v1" + index + len
const COPROC_NODE_PREFIX: usize = 23; // "eu-id-s4-ligero-node-v1"

const BEST_OF: usize = 3;

/// One (invocation-count, input-length) work item: `count` hash calls each over
/// a buffer of `bytes` length.
#[derive(Clone, Copy)]
struct HashItem {
    count: u64,
    bytes: usize,
}

/// Build the exact hash-node work list for the three STARK trees.
fn stark_work() -> Vec<HashItem> {
    let mut items = Vec::new();
    for tree in STARK_TREES {
        // committed_log -> n_cols
        let mut cols_by_clog: std::collections::BTreeMap<u32, usize> = Default::default();
        for &(base_log, n) in *tree {
            *cols_by_clog.entry(base_log + LOG_BLOWUP).or_default() += n;
        }
        let height = *cols_by_clog.keys().max().unwrap();
        for d in (0..=height).rev() {
            let n_nodes = 1u64 << d;
            let child = if d < height { CHILD_BYTES } else { 0 };
            let vals = cols_by_clog.get(&d).copied().unwrap_or(0) * M31_BYTES;
            items.push(HashItem {
                count: n_nodes,
                bytes: child + vals,
            });
        }
    }
    items
}

/// Build the exact hash-node work list for the coprocessor Ligero tree.
fn coproc_work() -> Vec<HashItem> {
    let leaves = COPROC_CODEWORD_LEN as u64;
    let internal = leaves - 1;
    vec![
        HashItem {
            count: leaves,
            bytes: COPROC_LEAF_PREFIX + COPROC_COMMITTED_ROWS * COPROC_FIELD_BYTES,
        },
        HashItem {
            count: internal,
            bytes: COPROC_NODE_PREFIX + CHILD_BYTES,
        },
    ]
}

fn total_invocations(items: &[HashItem]) -> u64 {
    items.iter().map(|i| i.count).sum()
}
fn total_bytes(items: &[HashItem]) -> u64 {
    items.iter().map(|i| i.count * i.bytes as u64).sum()
}

// ---- Hash kernels. Each hashes `buf[..bytes]` and consumes the digest so the
// optimizer cannot elide the call. `acc` xors the first digest byte back in. ----
fn run_blake2s(items: &[HashItem], buf: &[u8]) -> u8 {
    let mut acc = 0u8;
    for it in items {
        let input = &buf[..it.bytes];
        for _ in 0..it.count {
            let mut h = Blake2s256::new();
            h.update(input);
            let d = h.finalize();
            acc ^= d[0];
        }
    }
    acc
}

fn run_blake3(items: &[HashItem], buf: &[u8]) -> u8 {
    let mut acc = 0u8;
    for it in items {
        let input = &buf[..it.bytes];
        for _ in 0..it.count {
            let d = blake3::hash(input);
            acc ^= d.as_bytes()[0];
        }
    }
    acc
}

fn run_sha256(items: &[HashItem], buf: &[u8]) -> u8 {
    let mut acc = 0u8;
    for it in items {
        let input = &buf[..it.bytes];
        for _ in 0..it.count {
            let mut h = Sha256::new();
            h.update(input);
            let d = h.finalize();
            acc ^= d[0];
        }
    }
    acc
}

fn best_of<F: FnMut() -> u8>(mut f: F) -> Duration {
    let mut best = Duration::MAX;
    for _ in 0..BEST_OF {
        let t = Instant::now();
        let acc = f();
        let e = t.elapsed();
        std::hint::black_box(acc);
        best = best.min(e);
    }
    best
}

/// Throughput sanity: assert SHA-256 uses the hardware extension (≥ 1.5 GB/s
/// single-thread). A pure-software SHA-256 tops out well under 1 GB/s.
fn sha256_throughput_gbs() -> f64 {
    let buf = vec![0xa5u8; 1 << 20]; // 1 MiB
    let iters = 256u64; // 256 MiB total
    let t = Instant::now();
    let mut acc = 0u8;
    for _ in 0..iters {
        let mut h = Sha256::new();
        h.update(&buf);
        acc ^= h.finalize()[0];
    }
    let e = t.elapsed();
    std::hint::black_box(acc);
    let bytes = iters * (buf.len() as u64);
    (bytes as f64) / e.as_secs_f64() / 1e9
}

#[test]
#[ignore = "measure-only bake-off; run with --ignored --nocapture"]
fn hasher_bakeoff() {
    // Guard: this is a single-thread measurement. Warn loudly if not pinned.
    match std::env::var("RAYON_NUM_THREADS").as_deref() {
        Ok("1") => {}
        other => eprintln!(
            "WARNING: RAYON_NUM_THREADS={other:?} (expected \"1\"). Hashers are \
             single-thread regardless, but pin it for reproducibility."
        ),
    }

    let sha_gbs = sha256_throughput_gbs();
    eprintln!("\nSHA-256 throughput sanity: {sha_gbs:.2} GB/s single-thread (1 MiB blocks)");
    assert!(
        sha_gbs >= 1.5,
        "SHA-256 throughput {sha_gbs:.2} GB/s < 1.5 GB/s — hardware SHA \
         extension NOT active; results would not reflect ARMv8 crypto. Build \
         with the sha2 `asm` feature on an aarch64 target."
    );

    let stark = stark_work();
    let coproc = coproc_work();

    // Shared scratch buffer sized to the largest node input across both trees.
    let max_bytes = stark
        .iter()
        .chain(coproc.iter())
        .map(|i| i.bytes)
        .max()
        .unwrap();
    let buf = vec![0x5au8; max_bytes];

    struct Row {
        name: &'static str,
        f: fn(&[HashItem], &[u8]) -> u8,
    }
    let hashers = [
        Row {
            name: "Blake2s",
            f: run_blake2s,
        },
        Row {
            name: "Blake3",
            f: run_blake3,
        },
        Row {
            name: "SHA-256(hw)",
            f: run_sha256,
        },
    ];

    for (label, items) in [("stark_trees(x3)", &stark), ("coproc_ligero", &coproc)] {
        eprintln!(
            "\n== {label}: {} hash invocations, {:.1} MB hashed input ==",
            total_invocations(items),
            total_bytes(items) as f64 / 1e6
        );
    }

    // Measure and print a table: ms/tree best-of-3 per (tree, hasher).
    eprintln!(
        "\n{:<14} {:>18} {:>18}",
        "hasher", "stark_trees ms", "coproc ms"
    );
    let mut stark_ms = [0f64; 3];
    let mut coproc_ms = [0f64; 3];
    for (i, h) in hashers.iter().enumerate() {
        let sd = best_of(|| (h.f)(&stark, &buf)).as_secs_f64() * 1e3;
        let cd = best_of(|| (h.f)(&coproc, &buf)).as_secs_f64() * 1e3;
        stark_ms[i] = sd;
        coproc_ms[i] = cd;
        eprintln!("{:<14} {:>18.2} {:>18.2}", h.name, sd, cd);
    }

    // Project proof time if a hasher replaces Blake2s.
    // STARK tree commits use about 17 percent of proof time.
    // The measured coprocessor Merkle time is about 79 ms.
    // Scale each tree linearly from its Blake2s baseline.
    // Exclude channel absorption because its transcript volume is small.
    // Measured coprocessor Merkle time.
    const COPROC_MERKLE_MEASURED_MS: f64 = 79.0;
    // A 1723 ms proof sample spent 17 percent on STARK tree commitments.
    const STARK_PROVE_MS: f64 = 1723.0;
    const STARK_COMMIT_SHARE: f64 = 0.17;
    let stark_commit_ms = STARK_PROVE_MS * STARK_COMMIT_SHARE;

    eprintln!("\n-- projected prove delta vs Blake2s baseline --");
    eprintln!(
        "baseline anchors: stark tree-commit ≈ {stark_commit_ms:.0} ms (17% of {STARK_PROVE_MS:.0}), \
         coproc merkle ≈ {COPROC_MERKLE_MEASURED_MS:.0} ms"
    );
    eprintln!(
        "{:<14} {:>16} {:>16} {:>16}",
        "hasher", "stark Δms", "coproc Δms", "total Δms"
    );
    for i in 0..3 {
        // scale the measured baseline commit ms by (this hasher kernel / blake2s kernel)
        let stark_scaled = stark_commit_ms * (stark_ms[i] / stark_ms[0]);
        let coproc_scaled = COPROC_MERKLE_MEASURED_MS * (coproc_ms[i] / coproc_ms[0]);
        let stark_delta = stark_scaled - stark_commit_ms;
        let coproc_delta = coproc_scaled - COPROC_MERKLE_MEASURED_MS;
        eprintln!(
            "{:<14} {:>16.1} {:>16.1} {:>16.1}",
            hashers[i].name,
            stark_delta,
            coproc_delta,
            stark_delta + coproc_delta
        );
    }
    eprintln!(
        "\n(negative Δ = faster than Blake2s. Kernel-replay isolates hash cost; \
         real stwo committer has SIMD packing not modeled here — treat magnitudes \
         as an upper bound on the achievable swing.)\n"
    );
}
