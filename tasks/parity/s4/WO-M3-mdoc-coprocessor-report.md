# WO-M3 mdoc Coprocessor Report

Date: 2026-07-04  
Branch: `codex/wo-m3-mdoc-coprocessor`  
Source ruling: `/Users/lucas/eu-id/tasks/parity/mailbox/answers/Q-M1-004.md`

## Summary

Q-M1-004 gives the implementation go-ahead: mdoc already exposes issuer and
device ECDSA `z` values as public statement inputs, so replacing private-z
DigestBind + P256 AIR with PublicDigestBind + a public coprocessor statement is
a privacy no-op relative to current mdoc v1.

The default mdoc circuit now removes the issuer and device P256 AIR modules and
their private digest bridges. It proves:

1. issuer SHA
2. issuer PublicDigestBind
3. device SHA
4. device PublicDigestBind
5. birth-date SHA
6. birth-date public bind
7. nationality SHA
8. nationality public bind
9. age predicate
10. nationality predicate
11. final mdoc coprocessor binding module

The legacy P256 AIR composition remains available with
`--no-default-features`.

## Implementation

- `MdocCircuitProof` carries issuer/device public digest-bind interaction
  claims plus one mdoc coprocessor bundle on the `ec-coprocessor` path.
- The verifier reconstructs issuer and device coprocessor statements from its
  own `MdocCircuitStatement`, never from proof bytes.
- The transcript absorb order is explicitly tagged and ordered as
  `issuer`, then `device`, followed by seed draw, batch bundle verification,
  and bundle-hash rejoin.
- The implementation reuses the shared `public_digest_bind.rs` component and
  the existing M2 batch coprocessor API.
- `mdoc_perf_probe` was added as a fixed-N release probe for WO gates:
  median prove, median verify, proof bytes, PCS config, and shape cells.

## Negatives

The ignored production-verifier mdoc negative suite passed:

- missing bundle rejects with `Error::CoprocessorMissing`
- tampered bundle rejects
- issuer SHA/public-z mismatch rejects
- device SHA/public-z mismatch rejects
- cross-slot `z` swap rejects
- cross-signature issuer/device swap rejects
- identity coprocessor bundle replay rejects
- issuer/device transcript order changes the fork/seed/rejoin digests
- tampered bundle changes the rejoin digest
- skipping rejoin changes the next STARK challenge

## Verification

All commands were run from
`/Users/lucas/eu-id/.claude/worktrees/wo-m1-coprocessor-merge`.

```bash
rtk proxy cargo check -p eu-id-prover
rtk proxy cargo check -p eu-id-prover --no-default-features
rtk proxy cargo test -p eu-id-prover --no-run
rtk proxy cargo test -p eu-id-prover --no-default-features --no-run
rtk proxy cargo test -p eu-id-prover --test mdoc_support
rtk proxy cargo test -p eu-id-prover --no-default-features --test mdoc_support
rtk proxy cargo test -p eu-id-prover mdoc_coprocessor_ -- --ignored
rtk proxy cargo test -p eu-id-prover --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies -- --ignored
rtk proxy cargo test -p eu-id-prover --no-default-features --test mdoc_support isolated_mdoc_circuit_profile_proves_and_verifies -- --ignored
rtk proxy cargo check -p eu-id-prover --example mdoc_perf_probe
rtk proxy cargo check -p eu-id-prover --no-default-features --example mdoc_perf_probe
```

## Perf

Command shape:

```bash
rtk proxy env RAYON_NUM_THREADS=1 BENCH_ITERS=5 cargo run -p eu-id-prover --release --example mdoc_perf_probe
rtk proxy env RAYON_NUM_THREADS=1 BENCH_ITERS=5 cargo run -p eu-id-prover --release --no-default-features --example mdoc_perf_probe
```

`BENCH-LOCK` was requested by Q-M1-004, but no `BENCH-LOCK` file exists in this
worktree or in `/Users/lucas/eu-id`.

| metric | legacy P256 AIR | default coprocessor | delta |
|---|---:|---:|---:|
| prove median, N=5 | 7,866 ms | 5,266 ms | -2,600 ms (-33.1%) |
| verify median, N=5 | 40 ms | 46 ms | +6 ms |
| proof bytes | 4,563,243 | 1,834,614 | -2,728,629 (-59.8%) |
| committed shape cells | 79,988,576 | 56,296,064 | -23,692,512 (-29.6%) |

The remaining default in-STARK shape is almost entirely the four SHA modules:
56,276,096 / 56,296,064 cells. The coprocessor bundle is external to that STARK
shape count.
