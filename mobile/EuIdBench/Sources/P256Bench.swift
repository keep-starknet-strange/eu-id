import SwiftUI
import CryptoKit
import Foundation

// Proves and verifies one P-256 ECDSA signature on the device.
// CryptoKit creates the key and signature.
// The Rust prover receives the raw `z`, `r`, `s`, `Qx`, and `Qy` values.
// CryptoKit independently verifies the signature.
enum P256Bench {
    // The fixed private key gives the same public key in each run.
    // ECDSA uses a new nonce, so each signature can be different.
    // This difference does not change the proof workload.
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
        // Use CryptoKit to sign the message.
        // Give the FFI five 32-byte big-endian field elements.
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
        let verified = raw.verified == 1
        let peakMiB = Double(raw.peak_bytes) / (1024 * 1024)

        // Check that the prover result agrees with the CryptoKit result.
        let cryptoKitValid = publicKey.isValidSignature(signature, for: message)
        let agrees = verified == cryptoKitValid
        let ok = raw.ok == 1 && verified && agrees

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

    // Keeps all five 32-byte buffers valid during the FFI call.
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
            blurb: "Proves and verifies one P-256 ECDSA signature on the device. "
                + "CryptoKit signs the message and independently verifies the signature. "
                + "Rust measures peak memory.",
            cases: P256Bench.cases
        )
    }
}

#Preview {
    P256BenchView()
}
