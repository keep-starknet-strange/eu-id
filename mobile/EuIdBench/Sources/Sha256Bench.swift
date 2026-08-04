import SwiftUI
import CryptoKit
import Foundation

// Proves and verifies the standalone SHA-256 statement on the device.
// CryptoKit independently calculates and checks the digest.
enum Sha256Bench {
    // Uses the FIPS `abc` vector and three messages that contain `0xAB`.
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

    // Calls the Rust C ABI and checks the digest with CryptoKit.
    private static func bench(label: String, message: [UInt8]) -> BenchResult {
        let raw: EuIdBench = message.withUnsafeBufferPointer { buf in
            eu_id_bench_sha256(buf.baseAddress, buf.count, 1)
        }

        let digestBytes = withUnsafeBytes(of: raw.digest) { Array($0) }
        let digestHex = digestBytes.map { String(format: "%02x", $0) }.joined()
        let expected = Array(SHA256.hash(data: Data(message)))
        let matches = digestBytes == expected
        let peakMiB = Double(raw.peak_bytes) / (1024 * 1024)
        let ok = raw.ok == 1 && matches

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
            blurb: "Runs the standalone SHA-256 prover on the device. "
                + "Each run proves and verifies the statement. Rust measures peak memory.",
            cases: Sha256Bench.cases
        )
    }
}

#Preview {
    Sha256BenchView()
}
