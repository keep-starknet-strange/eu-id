import SwiftUI

// eu-id mobile benchmark harness. Drives the Rust provers via the
// eu_id_bench_identity / eu_id_bench_sha256 / eu_id_bench_p256 C ABI and shows
// prove/verify time and peak footprint, in a tab per workload: the combined,
// cross-bound identity proof (the headline) plus its standalone SHA-256 and
// P-256 ECDSA components.
@main
struct EuIdBenchApp: App {
    init() {
        // Scripted/CI path: `--autorun` runs every case once and logs, no taps.
        if HeadlessRunner.isEnabled {
            HeadlessRunner.runAllAndLog()
        }
    }

    var body: some Scene {
        WindowGroup {
            ContentView()
        }
    }
}
