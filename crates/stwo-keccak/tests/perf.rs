//! Performance + cost accounting for the acceptance gates. Run with:
//!   cargo test -p stwo-keccak --test perf --release -- --nocapture
//!
//! Reports:
//!   - committed cells per permutation (base + interaction), counted from the
//!     component shapes;
//!   - single-thread prove time for a >= 22-permutation chain, and ms/perm;
//!   - total preprocessed table cells.

use std::time::Instant;

use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::prover::backend::simd::m31::N_LANES;
use stwo_keccak::keccak;
use stwo_keccak::keccak_round;
use stwo_keccak::tables_air::PREPROCESSED_CELLS;
use stwo_keccak::{prove_shake256, verify_shake256};

const N_ROUNDS: usize = 24;

/// Batch-4 logup constraints have log-degree excess 2, so proving needs
/// `log_blowup >= 2` (production uses 3).
fn pcs_config() -> PcsConfig {
    PcsConfig {
        fri_config: FriConfig::new(0, 2, 3, 1),
        ..PcsConfig::default()
    }
}

/// Committed M31 cells per permutation, **house counting method**: one
/// permutation is proven as 24 `keccak_round` rows plus one `keccak` row.
/// `N_COMMITTED_COLUMNS` already counts each QM31 interaction column as
/// `SECURE_EXTENSION_DEGREE` (=4) M31 columns, so this is
/// `round_cols·24 + keccak_cols` — the raw committed footprint of one
/// permutation's worth of rows (columns × rows), *not* divided by `N_LANES`.
fn cells_per_perm() -> usize {
    keccak_round::N_COMMITTED_COLUMNS * N_ROUNDS + keccak::N_COMMITTED_COLUMNS
}

/// Amortized per-permutation cell footprint (divided across the `N_LANES` SIMD
/// permutations proven by one column set) — reported for context only.
fn amortized_cells_per_perm() -> usize {
    cells_per_perm() / N_LANES
}

#[test]
fn report_cell_counts() {
    let round = keccak_round::N_COMMITTED_COLUMNS;
    let keccak = keccak::N_COMMITTED_COLUMNS;
    println!("keccak_round committed columns/row (base+interaction, QM31 as 4 M31) = {round}");
    println!("keccak       committed columns/row (base+interaction, QM31 as 4 M31) = {keccak}");
    println!(
        "committed cells per permutation (M31, cols×rows: {round}×{N_ROUNDS}+{keccak}) = {} (target <= 75000)",
        cells_per_perm()
    );
    println!(
        "  amortized over {N_LANES} SIMD lanes = {}",
        amortized_cells_per_perm()
    );
    println!("preprocessed table cells (all 9 tables) = {PREPROCESSED_CELLS}");
    let lookups = 2 // keccak_round chain links
        + keccak_round::N_XOR3_LOOKUPS
        + keccak_round::N_ANDNOT_LOOKUPS
        + keccak_round::N_SPLIT_LOOKUPS;
    println!(
        "lookups/round = {lookups} (xor3 {} + andnot {} + split {} + 2 links; M3 was 1024+2)",
        keccak_round::N_XOR3_LOOKUPS,
        keccak_round::N_ANDNOT_LOOKUPS,
        keccak_round::N_SPLIT_LOOKUPS,
    );
    assert!(
        cells_per_perm() <= 75_000,
        "cells/perm {} exceeds the 75k budget",
        cells_per_perm()
    );
}

#[test]
fn prove_22_perm_chain() {
    // A message whose absorb+squeeze forces >= 22 permutations. Each 136-byte
    // absorb block is one permutation; ~21 blocks + squeeze gives >= 22.
    let msg_len = 136 * 21; // 21 absorb blocks
    let msg: Vec<u8> = (0..msg_len as u32)
        .map(|i| (i.wrapping_mul(97) & 0xFF) as u8)
        .collect();
    let n_squeeze = 2;

    // Warm the twiddle cache / preprocessed tables with a tiny prove first so the
    // timed run measures steady-state proving, not one-off setup.
    let _ = prove_shake256(b"warmup", 1, pcs_config()).expect("warmup");

    let start = Instant::now();
    let proof = prove_shake256(&msg, n_squeeze, pcs_config()).expect("prove");
    let elapsed = start.elapsed();

    let n_perms = proof.shape.n_perms();
    assert!(n_perms >= 22, "expected >= 22 perms, got {n_perms}");
    verify_shake256(&proof).expect("verify");

    let ms = elapsed.as_secs_f64() * 1000.0;
    let ms_per_perm = ms / n_perms as f64;
    println!("permutations = {n_perms}");
    println!("prove time   = {ms:.1} ms");
    println!("ms / perm    = {ms_per_perm:.3} (target <= 11)");
}

#[test]
fn prove_large_chain_amortized() {
    // A larger chain to observe the amortized ms/perm once the fixed 2^16 table
    // commitment + FRI cost is spread over many permutations (the ML-DSA regime).
    let msg_len = 136 * 200; // 200 absorb blocks
    let msg: Vec<u8> = (0..msg_len as u32)
        .map(|i| (i.wrapping_mul(97) & 0xFF) as u8)
        .collect();
    let _ = prove_shake256(b"warmup", 1, pcs_config()).expect("warmup");
    let start = Instant::now();
    let proof = prove_shake256(&msg, 2, pcs_config()).expect("prove");
    let elapsed = start.elapsed();
    let n_perms = proof.shape.n_perms();
    verify_shake256(&proof).expect("verify");
    let ms = elapsed.as_secs_f64() * 1000.0;
    println!("[large] permutations = {n_perms}");
    println!("[large] prove time   = {ms:.1} ms");
    println!("[large] ms / perm    = {:.3}", ms / n_perms as f64);
}
