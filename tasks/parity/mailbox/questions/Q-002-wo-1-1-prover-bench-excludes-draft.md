---
wo: WO-1.1
blocking: true
status: answered
---
## Question
WO-1.1 acceptance says `BM_ECDSAZKProver_equiv/1` single-thread must improve by at least 100 ms, but `crates/eu-id-prover/benches/common/longfellow_equiv.rs` builds `P256ProofDraft`s before the Criterion timed loop and times only `prove_current_air(draft)`. Should WO-1.1 acceptance use the new `hint_gen_timing` draft-builder median instead, or should the benchmark harness be changed to include draft construction in `BM_ECDSAZKProver_equiv/1`?

## Context
The scoped code path now improves draft/hint generation:

- `RAYON_NUM_THREADS=1 cargo test -p stwo-p256 --release hint_gen_timing -- --ignored --nocapture`: checked 323.335 ms -> optimized 157.269 ms (2.06x).
- Default Rayon: checked 192.371 ms -> optimized 58.347 ms (3.30x; 5.54x versus the one-thread checked baseline).
- `cargo test -p stwo-p256 --release` passes: 319 passed, 11 ignored.
- `cargo test -p eu-id-prover --release` passes: 18 passed, 18 ignored.

But the WO acceptance bench does not include draft generation:

```rust
let drafts = p256_drafts(num_sigs);
group.bench_function(format!("BM_ECDSAZKProver_equiv/{num_sigs}"), |b| {
    b.iter(|| {
        for draft in &drafts {
            black_box(prove_current_air(draft).expect("P256 comparison proof builds"));
        }
    });
});
```

As a result, `RAYON_NUM_THREADS=1 cargo bench -p eu-id-prover --bench longfellow_equiv_bench -- BM_ECDSAZKProver_equiv/1` remains unchanged at `[1.8652 s 1.8739 s 1.8843 s]`.

## My best guess
Use `hint_gen_timing` as the WO-1.1 metric and leave `BM_ECDSAZKProver_equiv/1` unchanged, because changing the benchmark harness would alter the parity benchmark definition and optimizing `prove_current_air` is outside WO-1.1's witness-construction scope.
