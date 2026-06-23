import SwiftUI
import Foundation

// Combined identity-proof benchmark: prove → verify the full cross-bound
// identity proof on-device (P256 ECDSA + SHA-256 + digest-bind bridge + age +
// nationality). This is the headline workload — the standalone SHA-256 / P-256
// tabs are its components. All shared run/display/logging lives in BenchKit;
// this file is just the case list + the per-case body.
enum IdentityBench {
    // The demo credential + policy the combined proof is driven from — the same
    // `valid_over_18` fixture the laptop benchmark uses (born 2000-01-01,
    // Germany; reference date 2026-06-17, min age 18, accepted {DE, FR, IT, ES}),
    // so the device numbers line up with the committed laptop results.
    static let acceptedNationalities: [UInt32] = [276, 250, 380, 724]

    private static func input(_ accepted: UnsafeBufferPointer<UInt32>) -> EuIdIdentityInput {
        EuIdIdentityInput(
            birth_year: 2000,
            birth_month: 1,
            birth_day: 1,
            nationality: 276,
            current_year: 2026,
            current_month: 6,
            current_day: 17,
            min_age_years: 18,
            accepted: accepted.baseAddress,
            accepted_len: accepted.count
        )
    }

    static var cases: [BenchCase] {
        [
            BenchCase(label: "identity", subtitle: "born 2000-01-01, DE") {
                // The combined prover overflows the default worker stack, so run
                // the FFI call on a dedicated 32 MB-stack thread (see BenchKit).
                onLargeStack { bench() }
            },
        ]
    }

    // Call the combined-prover C ABI. Measurement happens inside Rust; this just
    // marshals the demo credential + policy and cross-checks/logs the result.
    private static func bench() -> BenchResult {
        let label = "identity"
        let raw: EuIdIdentityBench = acceptedNationalities.withUnsafeBufferPointer { accepted in
            var input = input(accepted)
            return eu_id_bench_identity(&input, 1)
        }

        let ok = raw.ok == 1
        let peakMiB = Double(raw.peak_bytes) / (1024 * 1024)
        let proofKiB = Double(raw.proof_bytes) / 1024

        logBenchResult(
            label: label, ok: ok, proveMs: raw.prove_ms, verifyMs: raw.verify_ms, peakMiB: peakMiB,
            extras: [
                ("proof_kib", String(format: "%.1f", proofKiB)),
            ]
        )

        return BenchResult(
            label: label,
            ok: ok,
            proveMs: raw.prove_ms,
            verifyMs: raw.verify_ms,
            peakMiB: peakMiB,
            details: [
                BenchDetail("proof", String(format: "%.1f KiB", proofKiB)),
                BenchDetail("bound ✓", ok ? "prove + verify" : "FAILED", style: .status(ok: ok)),
            ]
        )
    }
}

struct IdentityBenchView: View {
    var body: some View {
        BenchScreen(
            navigationTitle: "Identity Bench",
            blurb: "Proves → verifies the full cross-bound identity proof on-device: "
                + "P256 ECDSA + SHA-256 + digest-bind bridge + age + nationality, over the "
                + "demo credential (born 2000-01-01, DE). Peak memory is measured inside Rust.",
            cases: IdentityBench.cases
        )
    }
}

#Preview {
    IdentityBenchView()
}
