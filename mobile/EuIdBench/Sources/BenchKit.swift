import SwiftUI
import Foundation
import os

// Shared benchmark UI + result model for the eu-id mobile harness. Each
// primitive (SHA-256, P-256) supplies a list of `BenchCase`s whose `body`
// drives the Rust C ABI and cross-checks the result; `BenchScreen` renders them
// identically. Keeping the run/display/logging here is the "generalization":
// adding a primitive is a new list of cases, not a new screen.

// Emits each result to the unified log so a host streaming the device log
// (idevicesyslog) can capture numbers without UI scraping. Grep "EUIDBENCH".
let benchLog = Logger(subsystem: "co.starkware.euid.bench", category: "bench")

// How a detail row renders beneath the common prove/verify/peak rows.
enum BenchDetailStyle {
    case plain                 // "key: value"
    case monospaced            // value only, small monospaced (e.g. a digest)
    case status(ok: Bool)      // "key: value", green when ok else red
}

// One algorithm-specific metric row.
struct BenchDetail: Identifiable {
    let id = UUID()
    let key: String
    let value: String
    let style: BenchDetailStyle

    init(_ key: String, _ value: String, style: BenchDetailStyle = .plain) {
        self.key = key
        self.value = value
        self.style = style
    }
}

// Result of one run, in display-ready form: common timing fields plus an
// ordered list of per-algorithm detail rows.
struct BenchResult: Identifiable {
    let id = UUID()
    let label: String
    let ok: Bool
    let proveMs: UInt64
    let verifyMs: UInt64
    let peakMiB: Double
    let details: [BenchDetail]

    static func failed(_ label: String) -> BenchResult {
        BenchResult(label: label, ok: false, proveMs: 0, verifyMs: 0, peakMiB: 0, details: [])
    }
}

// One runnable case: a label, an optional subtitle (size/source), and a body
// that performs the blocking FFI call + cross-check. `body` runs off the main
// thread (see `BenchScreen`), so it may block for seconds.
struct BenchCase: Identifiable {
    let id = UUID()
    let label: String
    let subtitle: String
    let body: () -> BenchResult

    init(label: String, subtitle: String = "", body: @escaping () -> BenchResult) {
        self.label = label
        self.subtitle = subtitle
        self.body = body
    }
}

// Machine-readable result line for host-side capture via idevicesyslog. NSLog
// (not just Logger) so it reaches the classic syslog stream. The "EUIDBENCH
// RESULT" prefix and common key=value fields are stable across primitives;
// `extras` carries algorithm-specific machine values (e.g. digest_match=1).
func logBenchResult(
    label: String,
    ok: Bool,
    proveMs: UInt64,
    verifyMs: UInt64,
    peakMiB: Double,
    extras: [(String, String)]
) {
    let extraStr = extras.map { "\($0.0)=\($0.1)" }.joined(separator: " ")
    NSLog("EUIDBENCH RESULT label=%@ ok=%d prove_ms=%llu verify_ms=%llu peak_mib=%.0f %@",
          label, ok ? 1 : 0, proveMs, verifyMs, peakMiB, extraStr)
    benchLog.log("RESULT label=\(label) ok=\(ok ? 1 : 0) prove_ms=\(proveMs) peak_mib=\(peakMiB)")
}

// Headless auto-run for scripted / CI testing. Launch the app with `--autorun`
// (e.g. `xcrun simctl launch <udid> co.starkware.euid.bench --autorun`) to run
// every case from both primitives once on a background queue, logging each as an
// "EUIDBENCH RESULT ..." line. Bracketed by "EUIDBENCH AUTORUN start/done" so a
// host capturing the device log knows when the sweep is complete.
enum HeadlessRunner {
    static var isEnabled: Bool { CommandLine.arguments.contains("--autorun") }

    static func runAllAndLog() {
        DispatchQueue.global(qos: .userInitiated).async {
            NSLog("EUIDBENCH AUTORUN start")
            // Identity first — the combined proof is the headline workload.
            for c in IdentityBench.cases { _ = c.body() }
            for c in Sha256Bench.cases { _ = c.body() }
            for c in P256Bench.cases { _ = c.body() }
            NSLog("EUIDBENCH AUTORUN done")
            // Headless/CI mode: exit so `devicectl --console` (or simctl) returns
            // with the full log flushed. Only reached under `--autorun`.
            exit(0)
        }
    }
}

// Reusable benchmark screen: a blurb, per-case run buttons + result rows, and a
// "run all" button. The SHA-256 and P-256 tabs are each just a `BenchScreen`
// with a different case list.
struct BenchScreen: View {
    let navigationTitle: String
    let blurb: String
    let cases: [BenchCase]

    @State private var results: [UUID: BenchResult] = [:]
    @State private var running: UUID? = nil
    @State private var runningAll = false

    var body: some View {
        NavigationStack {
            List {
                Section {
                    Text(blurb)
                        .font(.footnote)
                        .foregroundStyle(.secondary)
                }

                ForEach(cases) { c in
                    Section(c.label) {
                        Button {
                            run(c)
                        } label: {
                            HStack {
                                Text(buttonTitle(c))
                                Spacer()
                                if running == c.id {
                                    ProgressView()
                                }
                            }
                        }
                        .disabled(running != nil || runningAll)

                        if let r = results[c.id] {
                            resultRows(r)
                        }
                    }
                }

                Section {
                    Button("Run all (sequential)") { runAll() }
                        .disabled(running != nil || runningAll)
                }
            }
            .navigationTitle(navigationTitle)
        }
    }

    private func buttonTitle(_ c: BenchCase) -> String {
        c.subtitle.isEmpty ? "Prove \(c.label)" : "Prove \(c.label) (\(c.subtitle))"
    }

    @ViewBuilder
    private func resultRows(_ r: BenchResult) -> some View {
        if r.ok {
            LabeledContent("prove", value: "\(r.proveMs) ms")
            LabeledContent("verify", value: "\(r.verifyMs) ms")
            LabeledContent("peak", value: String(format: "%.0f MiB", r.peakMiB))
            ForEach(r.details) { d in
                switch d.style {
                case .plain:
                    LabeledContent(d.key, value: d.value)
                case .monospaced:
                    Text(d.value)
                        .font(.system(.caption2, design: .monospaced))
                        .foregroundStyle(.secondary)
                case .status(let ok):
                    LabeledContent(d.key, value: d.value)
                        .foregroundStyle(ok ? .green : .red)
                }
            }
        } else {
            Text("FAILED (prove/verify error or jetsam)")
                .foregroundStyle(.red)
        }
    }

    // Kick off one case on a background queue so the UI thread stays live
    // (the prove call can take many seconds).
    private func run(_ c: BenchCase) {
        running = c.id
        DispatchQueue.global(qos: .userInitiated).async {
            let r = c.body()
            DispatchQueue.main.async {
                results[c.id] = r
                running = nil
            }
        }
    }

    private func runAll() {
        runningAll = true
        DispatchQueue.global(qos: .userInitiated).async {
            for c in cases {
                let r = c.body()
                DispatchQueue.main.async { results[c.id] = r }
            }
            DispatchQueue.main.async { runningAll = false }
        }
    }
}

// Mutable reference cell used to carry a worker thread's result back to its
// caller (the semaphore in `onLargeStack` orders the write before the read).
private final class ResultBox<T> {
    var value: T?
}

// Run `work` on a dedicated thread with a large stack and block until it
// finishes. The combined STARK prover overflows the 512 KB default stack of a
// `DispatchQueue` worker thread (an EXC_BAD_ACCESS stack-guard fault); a 32 MB
// stack matches the headroom the laptop/main-thread prover has. The standalone
// SHA-256 / P-256 provers fit the default stack, so only the identity bench
// needs this. Call from a background queue (e.g. inside a `BenchCase.body`) so
// the blocking wait does not stall the UI.
func onLargeStack<T>(_ work: @escaping () -> T) -> T {
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
