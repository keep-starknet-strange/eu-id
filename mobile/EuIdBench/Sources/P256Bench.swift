import SwiftUI
import CryptoKit
import Foundation

// P-256 ECDSA benchmark: prove → verify one signature on-device. Swift/CryptoKit
// creates the keypair + signature and hands the raw (z, r, s, Qx, Qy) bytes to
// the Rust prover, then independently re-verifies — the honest analog of the
// SHA-256 digest cross-check. The AIR covers exactly one signature, so there is
// no message-size axis; the two cases differ only in where the key comes from.
enum P256Bench {
    // Fixed 32-byte private key → reproducible public key across runs. (ECDSA
    // signing still draws a fresh nonce, so the signature varies; the prove
    // workload — and thus the timing — does not.)
    static let fixtureKeyBytes = [UInt8](repeating: 7, count: 32)
    static let message = Data("eu-id mobile p256 bench fixture".utf8)

    static var cases: [BenchCase] {
        [
            BenchCase(label: "fixed key", subtitle: "deterministic") {
                bench(label: "fixed key",
                      key: try? P256.Signing.PrivateKey(rawRepresentation: Data(fixtureKeyBytes)))
            },
            BenchCase(label: "random key", subtitle: "fresh each run") {
                bench(label: "random key", key: P256.Signing.PrivateKey())
            },
        ]
    }

    private static func bench(label: String, key: P256.Signing.PrivateKey?) -> BenchResult {
        // Sign with CryptoKit (SHA-256 inside), then lay the statement out as
        // five 32-byte big-endian field elements — exactly what the FFI reads.
        guard let key, let signature = try? key.signature(for: message) else {
            logBenchResult(label: label, ok: false, proveMs: 0, verifyMs: 0, peakMiB: 0, extras: [])
            return .failed(label)
        }
        let publicKey = key.publicKey

        let z = [UInt8](SHA256.hash(data: message))     // 32
        let sig = [UInt8](signature.rawRepresentation)  // 64 = r||s
        let pub = [UInt8](publicKey.rawRepresentation)  // 64 = x||y
        let r = Array(sig[0..<32])
        let s = Array(sig[32..<64])
        let qx = Array(pub[0..<32])
        let qy = Array(pub[32..<64])

        let raw = callP256(z, r, s, qx, qy, iters: 1)
        let ok = raw.ok == 1
        let verified = raw.verified == 1
        let peakMiB = Double(raw.peak_bytes) / (1024 * 1024)

        // Independent verdict from CryptoKit; the cross-check passes iff the
        // prover's verified flag agrees with it.
        let cryptoKitValid = publicKey.isValidSignature(signature, for: message)
        let agrees = verified == cryptoKitValid

        logBenchResult(
            label: label, ok: ok, proveMs: raw.prove_ms, verifyMs: raw.verify_ms, peakMiB: peakMiB,
            extras: [
                ("verified", verified ? "1" : "0"),
                ("cryptokit_valid", cryptoKitValid ? "1" : "0"),
                ("cryptokit_match", agrees ? "1" : "0"),
            ]
        )

        return BenchResult(
            label: label,
            ok: ok,
            proveMs: raw.prove_ms,
            verifyMs: raw.verify_ms,
            peakMiB: peakMiB,
            details: [
                BenchDetail("verified", verified ? "yes" : "no", style: .status(ok: verified)),
                BenchDetail("CryptoKit ✓", agrees ? "matches" : "MISMATCH", style: .status(ok: agrees)),
            ]
        )
    }

    // Hold all five 32-byte buffers alive across the single FFI call.
    private static func callP256(
        _ z: [UInt8], _ r: [UInt8], _ s: [UInt8], _ qx: [UInt8], _ qy: [UInt8], iters: UInt32
    ) -> EuIdP256Bench {
        z.withUnsafeBufferPointer { zp in
            r.withUnsafeBufferPointer { rp in
                s.withUnsafeBufferPointer { sp in
                    qx.withUnsafeBufferPointer { xp in
                        qy.withUnsafeBufferPointer { yp in
                            eu_id_bench_p256(
                                zp.baseAddress, rp.baseAddress, sp.baseAddress,
                                xp.baseAddress, yp.baseAddress, iters
                            )
                        }
                    }
                }
            }
        }
    }
}

struct P256BenchView: View {
    var body: some View {
        BenchScreen(
            navigationTitle: "P-256 Bench",
            blurb: "Proves → verifies one P-256 ECDSA signature on-device. Swift/CryptoKit "
                + "signs and hands the raw (z, r, s, Qx, Qy) to the Rust prover, then "
                + "re-verifies independently. Peak memory is measured inside Rust.",
            cases: P256Bench.cases
        )
    }
}

#Preview {
    P256BenchView()
}
