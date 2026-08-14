import SwiftUI
import Foundation
import os

// Contains the shared result types and views for the mobile benchmarks.
// Each primitive supplies a list of `BenchCase` values.
// `BenchScreen` shows each list.

// Writes each result to the unified log.
// A host can capture the results with `idevicesyslog`.
// Search the log for `EUIDBENCH`.
let benchLog = Logger(subsystem: "co.starkware.euid.bench", category: "bench")

// Defines how a detail row appears below the common result rows.
enum BenchDetailStyle {
    case plain                 // Shows `key: value`.
    case monospaced            // Shows only the value in a small monospaced font.
    case status(ok: Bool)      // Shows `key: value` in green or red.
}

// Contains one algorithm-specific result row.
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

// Contains the common results and ordered detail rows for one run.
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

// Defines one runnable case.
// The body makes the blocking FFI call and checks the result.
// `BenchScreen` runs the body off the main thread.
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

// Writes a machine-readable result to the device log.
// `NSLog` sends the entry to the legacy syslog stream.
// The `EUIDBENCH RESULT` prefix and common fields are stable.
// `extras` contains algorithm-specific values.
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

// Runs all cases when the app starts with `--autorun`.
// The runner writes one `EUIDBENCH RESULT` record for each case.
// The start and done records identify the complete run.
enum HeadlessRunner {
    static var isEnabled: Bool { CommandLine.arguments.contains("--autorun") }

    static func runAllAndLog() {
        DispatchQueue.global(qos: .userInitiated).async {
            NSLog("EUIDBENCH AUTORUN start")
            for c in Sha256Bench.cases { _ = c.body() }
            for c in P256Bench.cases { _ = c.body() }
            NSLog("EUIDBENCH AUTORUN done")
            // Exit after the system flushes the complete log.
            exit(0)
        }
    }
}

// Shows a description, the cases, their results, and a run-all button.
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

    // Run one case on a background queue.
    // This keeps the user interface responsive during the proof.
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
