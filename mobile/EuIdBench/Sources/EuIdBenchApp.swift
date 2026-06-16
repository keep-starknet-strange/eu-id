import SwiftUI

// SHA-256 mobile benchmark harness. Drives the Rust prover via the
// eu_id_bench_sha256 C ABI and shows prove/verify time, peak footprint, and
// the claimed digest for the four message sizes from the laptop perf doc.
@main
struct EuIdBenchApp: App {
    var body: some Scene {
        WindowGroup {
            ContentView()
        }
    }
}
