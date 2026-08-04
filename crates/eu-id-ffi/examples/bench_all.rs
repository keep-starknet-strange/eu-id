//! Runs the FFI benchmark surface on the host.
//!
//! The mobile app calls the same SHA-256 and P-256 functions.
//! The benchmark runs four SHA-256 message sizes and one P-256 signature.
//! It prints a table and one machine-readable line for each case.
//!
//! ```bash
//! cargo run --release -p eu-id-ffi --example bench_all
//! ```

use eu_id_ffi::{eu_id_bench_p256, eu_id_bench_sha256};
use p256::ecdsa::signature::Signer;
use p256::ecdsa::{Signature, SigningKey};
use sha2::{Digest, Sha256};

fn main() {
    let cases: [(&str, Vec<u8>); 4] = [
        ("abc", b"abc".to_vec()),
        ("55B", vec![0xAB; 55]),
        ("512B", vec![0xAB; 512]),
        ("4KiB", vec![0xAB; 4096]),
    ];

    println!(
        "build: parallel (rayon) | {} logical cores",
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(0),
    );
    println!(
        "{:<6} {:>7} {:>10} {:>11} {:>11} {:>8}",
        "label", "blocks", "prove_ms", "verify_ms", "peak_mib", "digest"
    );

    for (label, msg) in &cases {
        // Three iterations produce a median that matches the laptop method.
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

    bench_p256();
}

fn bench_p256() {
    let signing_key = SigningKey::from_bytes((&[7u8; 32]).into()).expect("valid signing key");
    let message = b"eu-id-ffi p256 bench fixture";
    let signature: Signature = signing_key.sign(message);
    let public_key = signing_key.verifying_key().to_encoded_point(false);
    let z: [u8; 32] = Sha256::digest(message).into();
    let r: [u8; 32] = signature.r().to_bytes().into();
    let s: [u8; 32] = signature.s().to_bytes().into();
    let qx: [u8; 32] = public_key.x().expect("x")[..].try_into().expect("x len");
    let qy: [u8; 32] = public_key.y().expect("y")[..].try_into().expect("y len");

    let result = unsafe {
        eu_id_bench_p256(
            z.as_ptr(),
            r.as_ptr(),
            s.as_ptr(),
            qx.as_ptr(),
            qy.as_ptr(),
            1,
        )
    };
    let peak_mib = result.peak_bytes as f64 / (1024.0 * 1024.0);

    println!("\nP-256 ECDSA proof:");
    println!(
        "{:<14} {:>10} {:>11} {:>11} {:>9} {:>6}",
        "fixture", "prove_ms", "verify_ms", "peak_mib", "verified", "ok"
    );
    println!(
        "{:<14} {:>10} {:>11} {:>11.0} {:>9} {:>6}",
        "fixed key",
        result.prove_ms,
        result.verify_ms,
        peak_mib,
        result.verified,
        if result.ok == 1 { "ok" } else { "FAIL" }
    );
    println!(
        "RESULT label=p256 ok={} verified={} prove_ms={} verify_ms={} peak_mib={:.0}",
        result.ok, result.verified, result.prove_ms, result.verify_ms, peak_mib
    );
}
