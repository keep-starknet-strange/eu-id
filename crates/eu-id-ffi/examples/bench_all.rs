//! Host-side driver for the four benchmark message sizes — the same
//! `eu_id_bench_sha256` the mobile app calls, so laptop and phone numbers
//! come from one code path. Prints a table plus a machine-readable line.
//!
//! ```bash
//! cargo run --release -p eu-id-ffi --example bench_all                 # single-threaded
//! cargo run --release -p eu-id-ffi --example bench_all --features parallel  # rayon
//! ```

use eu_id_ffi::eu_id_bench_sha256;

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
}
