import SwiftUI

// Shows one tab for each workload.
// The tabs contain the standalone SHA-256 and P-256 components.
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
