import SwiftUI

// Root view: one tab per primitive. Each tab is a `BenchScreen` driven by its
// algorithm's case list (see Sha256Bench.swift / P256Bench.swift). The shared
// run/display/logging machinery lives in BenchKit.swift, so adding a primitive
// is a new tab + case list, not a new screen.
struct ContentView: View {
    var body: some View {
        TabView {
            Sha256BenchView()
                .tabItem { Label("SHA-256", systemImage: "number") }
            P256BenchView()
                .tabItem { Label("P-256", systemImage: "lock.shield") }
        }
    }
}

#Preview {
    ContentView()
}
