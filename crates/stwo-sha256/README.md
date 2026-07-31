# stwo-sha256

This crate implements the SHA-256 AIR for the TS13 identity proof.
It also provides a standalone SHA-256 proof API.

The AIR constrains:

- SHA-256 message padding;
- the message schedule;
- all 64 compression rounds;
- the initial hash value;
- the hash chain between message blocks;
- the final digest;
- the complete padded message stream for composed proofs.

The TS13 circuit uses shared range tables and separate SHA-256 instances.
It binds the private `IssuerSignedItem` and MSO bytes to their digests.

The standalone API is in `src/stark.rs`:

```rust
prove_sha256(message, &ProverConfig::default())
verify_sha256_proof(&proof)
```

Run the tests in release mode:

```bash
cargo test --locked --release -p stwo-sha256
```

This research implementation is not audited.
STWO is not zero knowledge.
