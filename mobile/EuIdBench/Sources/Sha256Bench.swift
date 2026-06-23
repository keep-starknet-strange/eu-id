import SwiftUI
import CryptoKit
import Foundation

// SHA-256 benchmark: prove → verify the standalone SHA-256 STARK on-device for
// four message sizes, cross-checking the prover's digest against CryptoKit.
// All shared run/display/logging lives in BenchKit; this file is just the case
// list + the per-case body.
enum Sha256Bench {
    // The four sizes mirror the laptop snapshot: the FIPS "abc" vector plus
    // 55 B / 512 B / 4 KiB filled with 0xAB.
    static let messages: [(label: String, bytes: [UInt8])] = [
        ("abc", Array("abc".utf8)),
        ("55B", Array(repeating: 0xAB, count: 55)),
        ("512B", Array(repeating: 0xAB, count: 512)),
        ("4KiB", Array(repeating: 0xAB, count: 4096)),
    ]

    static var cases: [BenchCase] {
        messages.map { m in
            BenchCase(label: m.label, subtitle: "\(m.bytes.count) B") {
                bench(label: m.label, message: m.bytes)
            }
        }
    }

    // Call the Rust C ABI and cross-check the digest with CryptoKit.
    private static func bench(label: String, message: [UInt8]) -> BenchResult {
        let raw: EuIdBench = message.withUnsafeBufferPointer { buf in
            eu_id_bench_sha256(buf.baseAddress, buf.count, 1)
        }

        let digestBytes = withUnsafeBytes(of: raw.digest) { Array($0) }
        let digestHex = digestBytes.map { String(format: "%02x", $0) }.joined()
        let expected = Array(SHA256.hash(data: Data(message)))
        let matches = digestBytes == expected
        let peakMiB = Double(raw.peak_bytes) / (1024 * 1024)
        let ok = raw.ok == 1

        logBenchResult(
            label: label, ok: ok, proveMs: raw.prove_ms, verifyMs: raw.verify_ms, peakMiB: peakMiB,
            extras: [
                ("blocks", "\(raw.n_blocks)"),
                ("digest_match", matches ? "1" : "0"),
                ("digest", digestHex),
            ]
        )

        return BenchResult(
            label: label,
            ok: ok,
            proveMs: raw.prove_ms,
            verifyMs: raw.verify_ms,
            peakMiB: peakMiB,
            details: [
                BenchDetail("blocks", "\(raw.n_blocks)"),
                BenchDetail("digest ✓", matches ? "matches" : "MISMATCH", style: .status(ok: matches)),
                BenchDetail("", digestHex, style: .monospaced),
            ]
        )
    }
}

struct Sha256BenchView: View {
    var body: some View {
        BenchScreen(
            navigationTitle: "SHA-256 Bench",
            blurb: "Runs the standalone SHA-256 STARK prover on-device. Each run does "
                + "prove → verify and measures peak memory inside Rust.",
            cases: Sha256Bench.cases
        )
    }
}

#Preview {
    Sha256BenchView()
}
