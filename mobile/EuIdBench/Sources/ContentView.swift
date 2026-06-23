import SwiftUI

// Root view: one tab per workload. Each tab is a `BenchScreen` driven by its
// case list (see IdentityBench.swift / Sha256Bench.swift / P256Bench.swift). The
// combined identity proof is the headline, so it is the first (default) tab; the
// SHA-256 and P-256 tabs are its standalone components. The shared
// run/display/logging machinery lives in BenchKit.swift, so adding a workload is
// a new tab + case list, not a new screen.
struct ContentView: View {
    var body: some View {
        TabView {
            IdentityBenchView()
                .tabItem { Label("Identity", systemImage: "person.text.rectangle") }
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
