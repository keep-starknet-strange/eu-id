import SwiftUI
import CryptoKit
import os

// Emits each result to the unified log so a host streaming the device log
// (idevicesyslog) can capture numbers without UI scraping. Grep "EUIDBENCH".
private let benchLog = Logger(subsystem: "co.starkware.euid.bench", category: "bench")

// One benchmark case = a labelled message. The four sizes mirror the laptop
// snapshot: the FIPS `"abc"` vector plus 55 B / 512 B / 4 KiB filled with 0xAB.
struct BenchCase: Identifiable {
    let id = UUID()
    let label: String
    let message: [UInt8]

    static let all: [BenchCase] = [
        BenchCase(label: "abc", message: Array("abc".utf8)),
        BenchCase(label: "55B", message: Array(repeating: 0xAB, count: 55)),
        BenchCase(label: "512B", message: Array(repeating: 0xAB, count: 512)),
        BenchCase(label: "4KiB", message: Array(repeating: 0xAB, count: 4096)),
    ]
}

// Result of one run, formatted for display.
struct BenchResult: Identifiable {
    let id = UUID()
    let label: String
    let ok: Bool
    let proveMs: UInt64
    let verifyMs: UInt64
    let peakMiB: Double
    let nBlocks: UInt64
    let digestHex: String
    // True iff the prover's digest matches an independent CryptoKit hash.
    let digestMatches: Bool
}

struct ContentView: View {
    @State private var results: [String: BenchResult] = [:]
    @State private var running: String? = nil
    @State private var runningAll = false

    var body: some View {
        NavigationStack {
            List {
                Section {
                    Text("Runs the standalone SHA-256 STARK prover on-device. "
                         + "Each run does prove → verify and measures peak memory "
                         + "inside Rust.")
                        .font(.footnote)
                        .foregroundStyle(.secondary)
                }

                ForEach(BenchCase.all) { c in
                    Section(c.label) {
                        Button {
                            run(c)
                        } label: {
                            HStack {
                                Text("Prove \(c.label) (\(c.message.count) B)")
                                Spacer()
                                if running == c.label {
                                    ProgressView()
                                }
                            }
                        }
                        .disabled(running != nil || runningAll)

                        if let r = results[c.label] {
                            resultRows(r)
                        }
                    }
                }

                Section {
                    Button("Run all (sequential)") { runAll() }
                        .disabled(running != nil || runningAll)
                }
            }
            .navigationTitle("SHA-256 Bench")
        }
    }

    @ViewBuilder
    private func resultRows(_ r: BenchResult) -> some View {
        if r.ok {
            LabeledContent("prove", value: "\(r.proveMs) ms")
            LabeledContent("verify", value: "\(r.verifyMs) ms")
            LabeledContent("peak", value: String(format: "%.0f MiB", r.peakMiB))
            LabeledContent("blocks", value: "\(r.nBlocks)")
            LabeledContent("digest ✓", value: r.digestMatches ? "matches" : "MISMATCH")
                .foregroundStyle(r.digestMatches ? .green : .red)
            Text(r.digestHex)
                .font(.system(.caption2, design: .monospaced))
                .foregroundStyle(.secondary)
        } else {
            Text("FAILED (prove/verify error or jetsam)")
                .foregroundStyle(.red)
        }
    }

    // Kick off one case on a background queue so the UI thread stays live
    // (the prove call can take many seconds).
    private func run(_ c: BenchCase) {
        running = c.label
        DispatchQueue.global(qos: .userInitiated).async {
            let r = Self.bench(c)
            DispatchQueue.main.async {
                results[c.label] = r
                running = nil
            }
        }
    }

    private func runAll() {
        runningAll = true
        DispatchQueue.global(qos: .userInitiated).async {
            for c in BenchCase.all {
                let r = Self.bench(c)
                DispatchQueue.main.async { results[c.label] = r }
            }
            DispatchQueue.main.async { runningAll = false }
        }
    }

    // Call the Rust C ABI and cross-check the digest with CryptoKit.
    private static func bench(_ c: BenchCase) -> BenchResult {
        let raw: EuIdBench = c.message.withUnsafeBufferPointer { buf in
            eu_id_bench_sha256(buf.baseAddress, buf.count, 1)
        }

        let digestBytes = withUnsafeBytes(of: raw.digest) { Array($0) }
        let digestHex = digestBytes.map { String(format: "%02x", $0) }.joined()
        let expected = Array(SHA256.hash(data: Data(c.message)))
        let matches = digestBytes == expected

        // Machine-readable line for host-side capture via idevicesyslog.
        // NSLog (not just Logger) so it reaches the classic syslog stream.
        NSLog("EUIDBENCH RESULT label=%@ ok=%d blocks=%llu prove_ms=%llu "
              + "verify_ms=%llu peak_mib=%.0f digest_match=%d digest=%@",
              c.label, raw.ok, raw.n_blocks, raw.prove_ms, raw.verify_ms,
              Double(raw.peak_bytes) / (1024 * 1024), matches ? 1 : 0, digestHex)
        benchLog.log("RESULT label=\(c.label) ok=\(raw.ok) prove_ms=\(raw.prove_ms) peak_mib=\(Double(raw.peak_bytes) / (1024 * 1024))")

        return BenchResult(
            label: c.label,
            ok: raw.ok == 1,
            proveMs: raw.prove_ms,
            verifyMs: raw.verify_ms,
            peakMiB: Double(raw.peak_bytes) / (1024 * 1024),
            nBlocks: raw.n_blocks,
            digestHex: digestHex,
            digestMatches: matches
        )
    }
}

#Preview {
    ContentView()
}
