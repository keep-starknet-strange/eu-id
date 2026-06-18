import SwiftUI
import CryptoKit
import os

// Emits each result to the unified log so a host streaming the device log
// (idevicesyslog) can capture numbers without UI scraping. Grep "EUIDBENCH".
private let benchLog = Logger(subsystem: "co.starkware.euid.bench", category: "bench")

// One SHA benchmark case = a labelled message. The four sizes mirror the laptop
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

// Result of one SHA run, formatted for display.
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

// Mutable reference cell used to carry a worker thread's result back to its
// caller (the semaphore in `onLargeStack` orders the write before the read).
private final class ResultBox<T> {
    var value: T?
}

// Result of one combined identity-proof run, formatted for display.
struct IdentityResult {
    let ok: Bool
    let proveMs: UInt64
    let verifyMs: UInt64
    let peakMiB: Double
    let proofKiB: Double
}

// The demo credential + policy the combined proof is driven from — the same
// `valid_over_18` fixture the laptop benchmark uses (born 2000-01-01, Germany;
// reference date 2026-06-17, min age 18, accepted {DE, FR, IT, ES}), so the
// device numbers line up with the committed laptop results.
private enum DemoIdentity {
    static let acceptedNationalities: [UInt32] = [276, 250, 380, 724]

    static func input(_ accepted: UnsafeBufferPointer<UInt32>) -> EuIdIdentityInput {
        EuIdIdentityInput(
            birth_year: 2000,
            birth_month: 1,
            birth_day: 1,
            nationality: 276,
            current_year: 2026,
            current_month: 6,
            current_day: 17,
            min_age_years: 18,
            accepted: accepted.baseAddress,
            accepted_len: accepted.count
        )
    }
}

struct ContentView: View {
    @State private var results: [String: BenchResult] = [:]
    @State private var running: String? = nil
    @State private var runningAll = false
    @State private var identity: IdentityResult? = nil
    @State private var runningIdentity = false

    private var busy: Bool { running != nil || runningAll || runningIdentity }

    var body: some View {
        NavigationStack {
            List {
                Section {
                    Text("Runs the eu-id STARK provers on-device and measures peak "
                         + "memory inside Rust. The combined identity proof is the "
                         + "headline; the SHA-256 cases are the standalone component.")
                        .font(.footnote)
                        .foregroundStyle(.secondary)
                }

                Section("Combined identity proof") {
                    Text("P256 ECDSA + SHA-256 + digest bridge + age + nationality, "
                         + "cross-bound, over the demo credential (born 2000-01-01, DE).")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                    Button {
                        runIdentity()
                    } label: {
                        HStack {
                            Text("Prove identity")
                            Spacer()
                            if runningIdentity { ProgressView() }
                        }
                    }
                    .disabled(busy)

                    if let r = identity {
                        identityRows(r)
                    }
                }

                ForEach(BenchCase.all) { c in
                    Section("SHA-256 · \(c.label)") {
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
                        .disabled(busy)

                        if let r = results[c.label] {
                            resultRows(r)
                        }
                    }
                }

                Section {
                    Button("Run all (sequential)") { runAll() }
                        .disabled(busy)
                }
            }
            .navigationTitle("eu-id Bench")
        }
        // Headless validation hook: launch with `--autorun-identity` (or
        // `--autorun-all`), or set `SIMCTL_CHILD_EUIDBENCH_AUTORUN`, to auto-run
        // the bench on launch so a simulator / CI run can capture numbers without
        // tapping the UI.
        .task {
            let args = CommandLine.arguments
            let env = ProcessInfo.processInfo.environment["EUIDBENCH_AUTORUN"]
            benchLog.log("autorun hook: args=\(args.joined(separator: ",")) env=\(env ?? "nil")")
            if args.contains("--autorun-all") || env == "all" {
                runAll()
            } else if args.contains("--autorun-identity") || env == "identity" {
                runIdentity()
            }
        }
    }

    @ViewBuilder
    private func identityRows(_ r: IdentityResult) -> some View {
        if r.ok {
            LabeledContent("prove", value: "\(r.proveMs) ms")
            LabeledContent("verify", value: "\(r.verifyMs) ms")
            LabeledContent("peak", value: String(format: "%.0f MiB", r.peakMiB))
            LabeledContent("proof", value: String(format: "%.1f KiB", r.proofKiB))
            LabeledContent("status", value: "ok")
                .foregroundStyle(.green)
        } else {
            Text("FAILED (prove/verify error or jetsam)")
                .foregroundStyle(.red)
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

    // Kick off the combined identity proof off the main thread so the UI stays
    // live (the prove call takes a couple of seconds).
    private func runIdentity() {
        runningIdentity = true
        DispatchQueue.global(qos: .userInitiated).async {
            let r = onLargeStack { Self.benchIdentity() }
            DispatchQueue.main.async {
                identity = r
                runningIdentity = false
            }
        }
    }

    // Kick off one SHA case off the main thread.
    private func run(_ c: BenchCase) {
        running = c.label
        DispatchQueue.global(qos: .userInitiated).async {
            let r = onLargeStack { Self.bench(c) }
            DispatchQueue.main.async {
                results[c.label] = r
                running = nil
            }
        }
    }

    private func runAll() {
        runningAll = true
        DispatchQueue.global(qos: .userInitiated).async {
            let id = onLargeStack { Self.benchIdentity() }
            DispatchQueue.main.async { identity = id }
            for c in BenchCase.all {
                let r = onLargeStack { Self.bench(c) }
                DispatchQueue.main.async { results[c.label] = r }
            }
            DispatchQueue.main.async { runningAll = false }
        }
    }

    // Run `work` on a dedicated thread with a large stack and block until it
    // finishes. The combined STARK prover overflows the 512 KB default stack of
    // a `DispatchQueue` worker thread (an EXC_BAD_ACCESS stack-guard fault); a
    // 32 MB stack matches the headroom the laptop/main-thread prover has. Call
    // from a background queue so the wait does not block the UI.
    private func onLargeStack<T>(_ work: @escaping () -> T) -> T {
        let box = ResultBox<T>()
        let done = DispatchSemaphore(value: 0)
        let thread = Thread {
            box.value = work()
            done.signal()
        }
        thread.stackSize = 32 * 1024 * 1024
        thread.start()
        done.wait()
        return box.value!
    }

    // Call the combined-prover C ABI. Measurement happens inside Rust; this just
    // marshals the demo credential + policy and logs a machine-readable line.
    private static func benchIdentity() -> IdentityResult {
        let raw: EuIdIdentityBench = DemoIdentity.acceptedNationalities
            .withUnsafeBufferPointer { accepted in
                var input = DemoIdentity.input(accepted)
                return eu_id_bench_identity(&input, 1)
            }

        // Machine-readable line for host-side capture via idevicesyslog.
        NSLog("EUIDBENCH RESULT label=identity ok=%d prove_ms=%llu verify_ms=%llu "
              + "peak_mib=%.0f proof_kib=%.1f",
              raw.ok, raw.prove_ms, raw.verify_ms,
              Double(raw.peak_bytes) / (1024 * 1024), Double(raw.proof_bytes) / 1024)
        benchLog.log("RESULT label=identity ok=\(raw.ok) prove_ms=\(raw.prove_ms) peak_mib=\(Double(raw.peak_bytes) / (1024 * 1024))")
        // Also to stdout so a `simctl launch --console` run can capture it.
        print(String(
            format: "RESULT label=identity ok=%d prove_ms=%llu verify_ms=%llu peak_mib=%.0f proof_kib=%.1f",
            raw.ok, raw.prove_ms, raw.verify_ms,
            Double(raw.peak_bytes) / (1024 * 1024), Double(raw.proof_bytes) / 1024))

        return IdentityResult(
            ok: raw.ok == 1,
            proveMs: raw.prove_ms,
            verifyMs: raw.verify_ms,
            peakMiB: Double(raw.peak_bytes) / (1024 * 1024),
            proofKiB: Double(raw.proof_bytes) / 1024
        )
    }

    // Call the SHA-256 C ABI and cross-check the digest with CryptoKit.
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
