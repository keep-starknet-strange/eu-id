import SwiftUI

// eu-id mobile benchmark harness. Drives the Rust provers via the
// eu_id_bench_sha256 / eu_id_bench_p256 C ABI and shows prove/verify time and
// peak footprint, in a tab per primitive (SHA-256 digests, P-256 ECDSA).
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
