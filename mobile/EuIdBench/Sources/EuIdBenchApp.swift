import SwiftUI

// Runs the eu-id mobile benchmarks through the Rust C ABI.
// Shows the proof time, verification time, and peak memory for each workload.
@main
struct EuIdBenchApp: App {
    init() {
        // Use `--autorun` to run and log each case without user input.
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
