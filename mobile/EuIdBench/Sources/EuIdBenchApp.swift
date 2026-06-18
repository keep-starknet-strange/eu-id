import SwiftUI

// eu-id mobile benchmark harness. Drives the Rust provers via the C ABI and
// shows prove/verify time and peak footprint: the combined, cross-bound identity
// proof (eu_id_bench_identity) as the headline, plus the standalone SHA-256
// component (eu_id_bench_sha256) across four message sizes.
@main
struct EuIdBenchApp: App {
    var body: some Scene {
        WindowGroup {
            ContentView()
        }
    }
}
