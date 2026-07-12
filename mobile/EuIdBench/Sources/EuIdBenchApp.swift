import SwiftUI

// Quantum-safe mobile benchmark harness. Drives the retained SHA-256 Rust ABI
// and displays prove/verify time and peak footprint.
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
