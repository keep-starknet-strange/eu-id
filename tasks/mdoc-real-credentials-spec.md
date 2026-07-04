# Real Wallet Credential Acceptance — Implementation Spec (plan phases A+B+C+E)

Goal: `prove_mdoc_circuit` accepts an ISO/IEC 18013-5 PID mdoc **as a real wallet
emits it**: canonical CBOR map ordering, text-form element values
(`"YYYY-MM-DD"`, alpha-2 nationality), x5chain issuer transport, detached
`DeviceAuthentication` device payload. Parent plan: `tasks/mdoc-full-impl-plan.md`
(this spec expands its phases A, B, C, E; phases D and F remain out of scope).
Self-contained: implement from this document plus the referenced files.

**Out of scope (do NOT touch):** in-circuit digest/device-key binding (Phase D —
digests and the device key stay public statement inputs), API promotion (Phase F),
privacy work, the POC identity path, `tasks/parity/`, the S4 track.

**House rules:** one phase = one landing (fast tests + the slow release mdoc proof
+ clippy + fmt green before moving on). Undecidable design point ⇒ STOP and write
a question to `tasks/mdoc-mailbox/questions/` (numbering continues from Q-001)
instead of guessing. Never weaken an existing test. `rtk` prefix on commands. Do
not commit — leave changes in the working tree and log progress in `tasks/todo.md`
following its existing checklist style. Perf gate: mdoc prove ≤ 2.0× POC
`prove_identity` single-thread (current: 1,797 ms vs 1,118 ms = 1.61×, quiet box,
N=5 — see perf-log); add a perf-log row per phase.

---

## Phase A — Multi-block SHA field exposure (`crates/stwo-sha256`)

The blocker for everything else. Today `FieldExposure::from_preimage_windows`
asserts every offset < 64 and yields are gated to `is_first_block`
(`src/field_exposure.rs`). Canonical CBOR puts element values past byte 64 of the
item preimage, and (Phase C) windows may STRADDLE a 64-byte block boundary — the
mechanism must be per-byte, not per-window.

### A.1 Hard constraint learned this session (do not violate)
Preprocessed tree-0 columns are deduped globally by ID and `air-core::prove` now
asserts ID ⇒ identical content (`assert_preprocessed_id_content_invariant`). The
SHA trace already has 10 log-dependent preprocessed columns under log-independent
IDs (`is_first_row` + 9 round-cyclic), which is why per-instance SHA sizing is
banned. **The block-gating mechanism must not add any preprocessed column whose
content depends on message length or window offsets.** Use witness (trace)
columns, which are per-instance by construction.

### A.2 Recommended mechanism (deviate only via mailbox)
1. **Block-counter witness column `b`** (one per SHA instance, only when any
   window needs block > 0): `b = 0` on the first block's rows (pin via the
   existing `is_first_block` boundary flag), constant within a block, increments
   by 1 across the `t = 63 → t = 0` boundary (the round position is available
   from the existing round-cyclic preprocessed columns; the block-chain
   constraint in `trace.rs` shows the boundary idiom).
2. **Per-window-byte selector `s`** (witness, 0/1): constrain `s·(s−1) = 0` and
   `s·(b − k) = 0` where `k` is the byte's block index (public constant baked
   into the eval, exactly like offsets are today). The exposure yield for that
   byte is multiplied by `s` on the schedule row of word `word_idx`
   (`offset_in_block / 4`, byte `offset_in_block % 4` — same resolution as
   today, just per-block).
3. **Soundness/completeness argument (put it in the module docs):** the selector
   can be non-zero only on rows of block `k` (constraint 2), so an exposed byte
   can only come from the claimed coordinate; the prover cannot *omit* the yield
   because the consuming predicate's LogUp requirement leaves the global balance
   broken — same one-sided-selector argument the existing exposure uses with
   `is_first_block`.
4. New constructor `FieldExposure::from_preimage_windows_multi(&[(field_id,
   abs_offset, len)])` resolving each byte to `(block_idx, word_idx,
   byte_in_word)`. **No straddle assertion** — bytes of one window may live in
   different blocks. Keep the old constructor and its block-0 fast path
   untouched (POC path uses it; zero new columns when all windows are block-0).

### A.3 Tests (all in `stwo-sha256`)
- Positive: 3-block message, windows in block 0, block 1, block 2, and one
  window straddling the block-1/2 boundary — all bind via the field relation.
- Negative: tamper one exposed byte ⇒ LogUp imbalance; set a selector on the
  wrong block in a hand-built trace ⇒ constraints unsatisfied; block counter
  frozen (not incremented) ⇒ constraints unsatisfied.
- Regression: existing exposure tests and the POC identity fast suite untouched
  and green; `assert_preprocessed_id_content_invariant` still passes with two
  SHA instances of different message lengths in one composition.

## Phase B — Text-form values in predicates (`crates/predicates`)

### B.1 Age from `"YYYY-MM-DD"` (10 exposed bytes)
New **text-date binding mode** on `AgeRangeCheck` alongside the packed mode:
- Bytes 4 and 7 constrained equal to `0x2D` ('-') — constants in the eval.
- The 8 digit bytes: constrain `dᵢ − 0x30 ∈ [0, 9]`. Follow the existing
  small-table idiom in `src/age/strategy/range_check/preprocessed.rs`
  (`day_delta_table` / `month_delta_table` are the pattern): one 10-entry
  preprocessed digit table (log 4 after padding), one multiplicity column, a
  LogUp use per digit. Do NOT add anything bigger; do NOT reuse the P256 range13
  tables across crates.
- Recomposition (linear, free): `year = 1000·d₀ + 100·d₁ + 10·d₂ + d₃`,
  `month = 10·d₄ + d₅`, `day = 10·d₆ + d₇`, fed into the existing age
  evaluation unchanged (semantic validity — month ≤ 12 etc. — is already the
  predicate's job).
- Mode selection lives in the mdoc composition: `from_extracted` knows the
  elementValue type; text values get the 10-byte window + text mode, `bstr(4)`
  values keep the packed mode (v1 fixtures must still prove).

### B.2 Nationality over alpha-2 ASCII
- The mdoc statement's accepted set becomes alpha-2: `Policy` (mdoc path) gains
  `accepted_nationalities_alpha2: Vec<[u8; 2]>`; the predicate table entry for
  each is `256·b₀ + b₁`. The exposed 2-byte window binds directly — the
  `numeric_country` mapping leaves the circuit path (keep it host-side for
  display in `ExtractedPidMdoc` only).
- The POC path keeps numeric codes untouched.

### B.3 Tests
Age text mode: proves on `"1990-07-15"`; a letter in the year ⇒ reject; wrong
separator byte ⇒ reject; recomposition cross-check vs host-parsed date in the
witness builder. Nat: alpha-2 membership positive + negative (`"DE"` in
{DE, FR}, `"US"` not). Packed-mode regressions green.

## Phase C — Canonical CBOR profile v2 (`crates/eu-id-prover/src/mdoc.rs` + fixtures)

- `IssuerSignedItem` keys in **RFC 8949 canonical order**: `random, digestID,
  elementValue, elementIdentifier` (shortest-encoded-key first). Element values
  as tstr (full-date, alpha-2). Fixture builder
  (`tests/mdoc_support.rs::fixture_with_values` + `issuer_signed_item`) emits
  canonical order; the parser must accept ANY key order (real wallets are the
  source of truth — parse by key name, never by position; it already does).
- `MdocCircuitStatement::from_extracted` changes: drop the
  window-within-block-0 check and the packed-bytes-at-offset requirement;
  replace with: window bytes at the offset equal the parsed value's text bytes
  (or packed bytes for v1-form values), any block. Offsets/windows are computed
  from the actual received encoding as today.
- Both forms prove: the slow release test runs the canonical-text fixture AND
  the v1 packed fixture. Update `docs/mdoc-credential-format.md` with a v2
  section (canonical order accepted, text values circuit-provable via Phase B);
  v1 stays valid.
- Expected perf note: a real-size MSO raises `shared_sha_log` (all four SHA
  instances, since per-instance sizing is banned) — record the delta in the
  perf-log row; it should be padding-scale, not provider-scale.

## Phase E — ISO device auth + x5chain (host-side only, `mdoc.rs`)

- **E1:** device signature payload = `cbor(["DeviceAuthentication",
  SessionTranscript, docType, DeviceNameSpacesBytes])` built host-side on both
  prove and verify sides from the verifier's own session transcript (replaces
  payload == raw transcript; keep the raw form accepted for the v1 fixtures).
  `z_device` stays verifier-recomputable public. `DeviceNameSpacesBytes` =
  tag-24 over an empty map for this profile.
- **E2:** accept `x5chain` (COSE header label **33**) in issuerAuth unprotected
  headers: parse the leaf certificate with the **`der` crate already in the
  tree** (via p256 — do NOT add `x509-cert` or any new dependency; a minimal
  walk to `SubjectPublicKeyInfo` via `spki` is enough), extract the P-256 key
  as the issuer key, and verify the chain to a caller-supplied trusted root
  out-of-circuit (signature-check each link with the `p256` crate; no
  revocation/validity-period checks on certs in v1 — document that). Bare
  `issuerKey` stays accepted for fixtures.
- Tests: wrong transcript ⇒ reject (update existing); x5chain fixture (self-
  signed 2-cert chain built in-test with the `p256` crate) extracts the right
  key; untrusted root ⇒ reject; malformed DER ⇒ typed error, no panic.

## Phase V — Real-vector gate (the acceptance criterion)

Obtain one real-shaped PID mdoc test vector: first choice, the test vectors in
`github.com/google/longfellow-zk` or `github.com/abetterinternet/zk-cred-longfellow`
(check the license file; Apache-2.0/MIT ⇒ vendor the vector bytes with an
attribution comment). Adapt only host-side glue (doctype/namespace/element names
via `MdocPidRequest`) — if the vector needs circuit-side changes beyond this
spec, STOP and mailbox with the exact mismatch. Gate: `extract_pid_mdoc` +
`prove_mdoc_circuit` + `verify_mdoc_circuit` pass end-to-end on it (slow test,
`#[ignore]`). If no usable vector exists in either repo, mailbox with what you
found instead of hand-crafting a fake "real" vector.

---

## Order, dependencies, sizing
A → B → C (needs A+B) → E → V. E is independent of A/B/C and may be done any
time. A is the critical path and the only new AIR surface (~40% of the chunk);
B medium; C/E light. After every phase: slow mdoc proof + perf-log row + todo.md
checklist entry. Total expectation ≈ 1.5–2 weeks of focused work, ~2k LOC.
