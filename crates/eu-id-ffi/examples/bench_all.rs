//! Host-side driver for the FFI benchmark surface — the same
//! `eu_id_bench_sha256` / `eu_id_bench_identity` the mobile app calls, so laptop
//! and phone numbers come from one code path. Runs the four SHA-256 message
//! sizes, then the combined, cross-bound identity proof (driven from the
//! canonical honest fixture). Prints a table plus a machine-readable line per
//! case.
//!
//! ```bash
//! cargo run --release -p eu-id-ffi --example bench_all                 # single-threaded
//! cargo run --release -p eu-id-ffi --example bench_all --features parallel  # rayon
//! ```

use eu_id_ffi::{eu_id_bench_identity, eu_id_bench_sha256, EuIdIdentityInput};
use eu_id_prover::fixtures;

fn main() {
    let cases: [(&str, Vec<u8>); 4] = [
        ("abc", b"abc".to_vec()),
        ("55B", vec![0xAB; 55]),
        ("512B", vec![0xAB; 512]),
        ("4KiB", vec![0xAB; 4096]),
    ];

    let threaded = cfg!(feature = "parallel");
    println!(
        "build: {} | {} logical cores",
        if threaded {
            "parallel (rayon)"
        } else {
            "single-threaded"
        },
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(0),
    );
    println!(
        "{:<6} {:>7} {:>10} {:>11} {:>11} {:>8}",
        "label", "blocks", "prove_ms", "verify_ms", "peak_mib", "digest"
    );

    for (label, msg) in &cases {
        // iters = 3: best-of/median, matching the laptop snapshot.
        let r = unsafe { eu_id_bench_sha256(msg.as_ptr(), msg.len(), 3) };
        let peak_mib = r.peak_bytes as f64 / (1024.0 * 1024.0);
        let digest_ok = if r.ok == 1 { "ok" } else { "FAIL" };
        println!(
            "{label:<6} {:>7} {:>10} {:>11} {:>11.0} {:>8}",
            r.n_blocks, r.prove_ms, r.verify_ms, peak_mib, digest_ok
        );
        println!(
            "RESULT label={label} ok={} blocks={} prove_ms={} verify_ms={} peak_mib={:.0}",
            r.ok, r.n_blocks, r.prove_ms, r.verify_ms, peak_mib
        );
    }

    bench_identity();
}

/// Run the combined, cross-bound identity proof (P256 + SHA + bridge + age +
/// nationality) over the canonical honest fixture. One iteration — the combined
/// prove is P256-dominated and slow.
fn bench_identity() {
    let fixture = fixtures::valid_over_18();
    let cred = fixture.signed.credential;
    let policy = fixture.policy;
    // `accepted` must outlive the call — `input` holds a raw pointer into it.
    let accepted = policy.accepted_nationalities.clone();
    let input = EuIdIdentityInput {
        birth_year: cred.birth_year,
        birth_month: cred.birth_month,
        birth_day: cred.birth_day,
        nationality: cred.nationality,
        current_year: policy.current_date.year as u16,
        current_month: policy.current_date.month as u8,
        current_day: policy.current_date.day as u8,
        min_age_years: policy.min_age_years,
        accepted: accepted.as_ptr(),
        accepted_len: accepted.len(),
    };

    let r = unsafe { eu_id_bench_identity(&input, 1) };
    let peak_mib = r.peak_bytes as f64 / (1024.0 * 1024.0);
    let proof_kib = r.proof_bytes as f64 / 1024.0;

    println!("\ncombined identity proof (P256 + SHA + bridge + age + nat):");
    println!(
        "{:<14} {:>10} {:>11} {:>11} {:>11} {:>6}",
        "fixture", "prove_ms", "verify_ms", "peak_mib", "proof_kib", "ok"
    );
    println!(
        "{:<14} {:>10} {:>11} {:>11.0} {:>11.1} {:>6}",
        fixture.name,
        r.prove_ms,
        r.verify_ms,
        peak_mib,
        proof_kib,
        if r.ok == 1 { "ok" } else { "FAIL" }
    );
    println!(
        "RESULT label=identity:{} ok={} prove_ms={} verify_ms={} peak_mib={:.0} proof_kib={:.1}",
        fixture.name, r.ok, r.prove_ms, r.verify_ms, peak_mib, proof_kib
    );
}
