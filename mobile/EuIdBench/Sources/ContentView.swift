import SwiftUI

// The quantum-safe mobile build currently exposes the standalone SHA-256
// benchmark. Shared run/display/logging machinery lives in BenchKit.swift.
struct ContentView: View {
    var body: some View {
        Sha256BenchView()
    }
}

#Preview {
    ContentView()
}
