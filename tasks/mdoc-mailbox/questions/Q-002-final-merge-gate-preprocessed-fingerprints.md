# Q-002 — final merge gate red: missing preprocessed fingerprints

During Phase M5 of `tasks/merge-plan.md`, the final gate

```bash
rtk proxy cargo test -p eu-id-prover --test nonce_signature --release -- --include-ignored
```

failed after M1 grouped commits, GKR parking, merge-source skips, and freeze-notice cleanup.

The failing tests were:

```text
identity_with_nonce_flow_rejects_wrong_nonce
identity_with_nonce_flow_verifies
identity_with_nonce_flow_rejects_wrong_device_key
```

The shared panic was:

```text
thread 'identity_with_nonce_flow_rejects_wrong_nonce' panicked at crates/air-core/src/lib.rs:306:9:
AirProver with preprocessed columns must expose preprocessed fingerprints

thread 'identity_with_nonce_flow_verifies' panicked at crates/air-core/src/lib.rs:306:9:
AirProver with preprocessed columns must expose preprocessed fingerprints

thread 'identity_with_nonce_flow_rejects_wrong_device_key' panicked at crates/air-core/src/lib.rs:306:9:
AirProver with preprocessed columns must expose preprocessed fingerprints
```

Full observed summary:

```text
running 7 tests
test nonce_signature_message_is_domain_separated ... ok
test nonce_signature_rejects_tampered_signature_before_proving ... ok
test identity_with_nonce_flow_rejects_wrong_nonce ... FAILED
test identity_with_nonce_flow_verifies ... FAILED
test identity_with_nonce_flow_rejects_wrong_device_key ... FAILED
test nonce_signature_proof_rejects_wrong_nonce ... ok
test nonce_signature_proof_verifies ... ok

test result: FAILED. 4 passed; 3 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.94s
```

Immediate context:

- The same gate passed before the grouped commits while the working tree still carried the full pre-merge state.
- After GKR parking, the target branch keeps the newer Stwo dependency/toolchain because the surviving WO sweep uses newer Stwo APIs.
- The red path is the six-module identity proof with both credential P-256 and nonce P-256 modules.
- Root-cause investigation has not been performed because the merge plan says to stop on any listed red gate and file this mailbox note instead of improvising.
