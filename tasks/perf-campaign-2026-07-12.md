# Perf campaign 2026-07-12

## WO-C1b redundancy argument

**Change:** deleted the `c6` scalar-bits claim family from the EC coprocessor
ECDSA circuit (`crates/eu-id-ec-coprocessor/src/ecdsa.rs`), compacted the
witness layout (removed `LayoutSlot::ScalarBits`, `LAYOUT_LEN` 2680 → 2168),
and dropped the now-orphaned `c3↔c6` u-scalar cross-family binding.

### Why c6 was redundant (verified against the code before deletion)

1. **What c6 asserted.** `build_c6_scalar_bits_circuit` (old ecdsa.rs:4336)
   proved (a) booleanity `bitᵢ² − bitᵢ = 0` for all 512 committed bits and
   (b) decomposition `Σ bitᵢ·2ⁱ = u1` (`C6_U1_INDEX`) and `= u2`
   (`C6_U2_INDEX`). The recompose outputs (indices 512/513) were terminal
   sumcheck outputs of c6 alone.

2. **The bits fed nothing else.** `c6_scalar_bits_input` (old ecdsa.rs:4394)
   was the *only* reader of `LayoutSlot::ScalarBits` (106..618) anywhere in the
   repo (exhaustive grep: the region is written by `write_scalar_bits` in
   `generate_witness` and read only by c6). The scalar-mult ladder is built
   from native `u1_words`/`u2_words` in `write_ladder_accumulators`
   (ecdsa.rs:444-452), not from the bits; its endpoints feed c11/c12/c13/c14-c15.

3. **c6's only cross-family output was redundant.** c6's u1/u2 (read from
   `LayoutSlot::UScalars`) were compared to c3-c5's u1/u2 via
   `verify_u_scalar_cross_family` — the single consumer of the c6 claims. Both
   families read the same `UScalars` slot, so the check only reconciled two
   committed copies of the same logical value.

4. **c3-c5 independently pins the stronger range fact.**
   `c3_c5_scalar_setup_input` (ecdsa.rs:4306) enters z,r,s via
   `Fp::from_bytes_be` (canonical, `< p`), and the c3-c5 layer constrains
   `u1 = z·s⁻¹ − q1·n` and `u2 = r·s⁻¹ − q2·n` (mod p). u1/u2 are base-field
   elements, so they are `< p < 2²⁵⁶` by construction — a range fact at least as
   strong as c6's `Σ bit < 2²⁵⁶`.

**Conclusion.** Deleting c6 removes (a) a booleanity/decomposition proof over
committed values consumed nowhere and (b) a redundant equality between two
committed copies of u1/u2 whose canonical range is already established (more
strongly) by c3-c5. The accepted `(z, r, s, Q)` set is provably unchanged. The
separate, pre-existing "ladder scalar unconstrained" gap is untouched: c6 never
bound the ladder's `u_words` to u1/u2 (only `bits → u1/u2`), so its removal
neither creates nor closes that gap.

Both sides of the deleted c3↔c6 binding were removed (mirroring the E1b
c9/c10↔c12 deletion): the c3 u-scalar consistency pins were dropped along with
all of c6, keeping the prover/verifier consistency cursor balanced.

### Numbers (RAYON_NUM_THREADS=1, BENCH_ITERS=5, ts13_full_probe, M-series)

| metric | before (730e9294) | after (WO-C1b) |
|---|---|---|
| committed_values (full N=1 tuple) | 31,121 | 27,920 |
| prove_ms_median (full) | 2,913 | 2,794 |
| verify_ms_median (full) | 265 | 240 |
| proof_bytes (full) | 4.52 MB | 4.44 MB (4,437,709) |
| proximity_openings bytes | — | 704,712 (+265,416 root_B) |
| claim_batch bytes / prove ms | — | 24,680 / 46.9 ms |
| bundle entry_count (3 ECDSA + MAC) | 25 | 22 |
| ECDSA family count | 8 | 7 |

committed_values dropped 3,201 (WO estimate was −3,141 for the c6 instance
input+pad ×3; the extra ~60 is the dropped c3/c6 u-scalar consistency pins).
Verify stays under the 280 ms bound. STARK side and preprocessed roots untouched
(the coprocessor witness layout is independent of the stwo preprocessed trace).

### Tests

- `cargo test --release -p eu-id-ec-coprocessor` green (47 incl. ignored
  full-bundle negatives; only pre-existing failure
  `gates::g4_gate_count_is_recorded_and_below_mailbox_gate`, missing inventory
  file, unrelated).
- `cargo test --release -p eu-id-prover` green incl. ignored end-to-end forgery
  negatives (`nonce_signature_proof_rejects_wrong_nonce`,
  `identity_with_nonce_flow_rejects_wrong_device_key/nonce`,
  `value_equality_element_identifier_anchor_offset_rejects_in_proof`).
- The c6 splice negative was repointed to a new `spliced_c11` negative (c11 had
  no splice test before), preserving one splice/tamper negative per remaining
  family boundary. Entry-count assertions updated 8→7 / 17→15 / 25→22.
