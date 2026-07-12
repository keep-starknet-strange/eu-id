//! Host driver for the SHA-256 mobile benchmark ABI.
//!
//! ```bash
//! cargo run --release -p eu-id-ffi --example bench_all
//! cargo run --release -p eu-id-ffi --example bench_all --features parallel
//! ```

use eu_id_ffi::eu_id_bench_sha256;

fn main() {
    let cases: [(&str, Vec<u8>); 4] = [
        ("abc", b"abc".to_vec()),
        ("55B", vec![0xAB; 55]),
        ("512B", vec![0xAB; 512]),
        ("4KiB", vec![0xAB; 4096]),
    ];

    println!(
        "build: {} | {} logical cores",
        if cfg!(feature = "parallel") {
            "parallel (rayon)"
        } else {
            "single-threaded"
        },
        std::thread::available_parallelism()
            .map(|count| count.get())
            .unwrap_or(0),
    );
    println!(
        "{:<6} {:>7} {:>10} {:>11} {:>11} {:>8}",
        "label", "blocks", "prove_ms", "verify_ms", "peak_mib", "digest"
    );

    for (label, message) in &cases {
        let result = unsafe { eu_id_bench_sha256(message.as_ptr(), message.len(), 3) };
        let peak_mib = result.peak_bytes as f64 / (1024.0 * 1024.0);
        println!(
            "{label:<6} {:>7} {:>10} {:>11} {:>11.0} {:>8}",
            result.n_blocks,
            result.prove_ms,
            result.verify_ms,
            peak_mib,
            if result.ok == 1 { "ok" } else { "FAIL" },
        );
        println!(
            "RESULT label={label} ok={} blocks={} prove_ms={} verify_ms={} peak_mib={peak_mib:.0}",
            result.ok, result.n_blocks, result.prove_ms, result.verify_ms,
        );
    }
}
