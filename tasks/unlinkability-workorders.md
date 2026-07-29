# Unlinkability campaign — work orders (feat/quantum-safe)

Scoped 2026-07-29 @ 41530e51+working-tree. The original campaign goal was
single-credential cryptographic unlinkability for the PQ mdoc proof. A-741
subsequently removed Phase 3/ZK from scope, so the authorized delivery claim
is narrower: post-quantum issuer and holder authentication with selective
disclosure, with no ZK or unlinkability claim.

Pre-repin baseline (measured, cold, 12-core Apple Silicon, fat-LTO release):
prove 587–616 ms / verify 76–79 ms / envelope ~952 KB (product path);
TS13 path 678–702 ms / 80–85 ms / ~971 KB. Keccak service = 37 perms,
`round_log_size` 2^10. PCS blowup-3 / 36q / pow20.

Post-`4f39939e` baseline (2026-07-29 acceptance, cold fresh processes):
product prove 507–513 ms / verify 74–80 ms / envelope 948,514–956,456 B;
TS13 prove 487–500 ms / fresh verify 34–38 ms / compressed wire
977,120–984,386 B. These improved numbers supersede the quoted pre-repin
timings; proof/wire shape remains in the same envelope-size band.

## Global rules (every WO)

- Work in a FRESH worktree branched off `feat/quantum-safe` HEAD (verify base
  commit before starting; do not base on main). Never read or touch other
  worktrees.
- Every shell command that mutates state starts with an absolute `cd` (cwd
  resets between calls).
- NEVER run `make` targets. Use `cargo` directly.
- Gates run with `RAYON_NUM_THREADS=1` (cross-session rayon deadlock).
  Performance numbers are measured WITHOUT that var, cold: fresh process,
  first iteration, ×3 runs, report all three.
- Perf acceptance is a named measured number per WO. No number ⇒ not done.
- Any change to constraints/components: invoke the `air-writer` skill first.
  Every constraint degree ≤ 2 where possible; the pinned stwo rev (4f877db2)
  supports composition bounds up to log_size+3, but each +1 bound doubles
  composition parts — justify anything above log_size+1 in the WO report.
- Every soundness-relevant change ships with NEGATIVE tests (tamper the
  witness, expect ConstraintsNotSatisfied / verify Err) proven to fail on
  revert.
- Existing test suite stays green: `cargo test --workspace` (961 tests) and
  the prover `--ignored` set.

Owner tags: **[agent-ready]** = fully specified, hand to an opus subagent
verbatim. **[design-first]** = needs a main-loop design pass before any agent
touches code.

---

## Phase 0 — spikes (measure before building)

### WO-U0a [agent-ready] — private-µ flip spike (Phase-1 cost, perf-faithful)

**What:** Measure the cost of moving the issuer ML-DSA instance to
private-message mode. Soundness-INCOMPLETE on purpose (native MSO fact checks
stay host-side); perf-faithful because the µ sponge + message byte relation are
the dominant adds.

**How:**
1. New example `crates/eu-id-prover/examples/unlink_spike_mu.rs`, cloned from
   `pq_perf_probe.rs`.
2. In a spike-local copy of the statement assembly (do NOT modify the
   production `prove_mdoc_circuit` path), switch the ISSUER instance from
   `MlDsaStatementProver::hosted_public(...)` (mdoc.rs:4342) to the
   private-message construction used by the REVOCATION instance at
   mdoc.rs:4368 (`hosted(...)` + `with_private_message()`); mirror its witness
   plumbing (µ sponge job: stwo-mldsa/src/statement.rs:200; message bytes
   bridged via `FieldBytesRelation`, statement.rs:426-429,
   sponge_link.rs:358-363). The device instance stays `hosted_public`.
3. The issuer Sig_structure (~2.5 KB fixture) is the private message. Host
   yields its bytes into the field-byte relation exactly as the revocation leg
   yields its 86-byte message — scale, don't redesign.
4. Prove + verify must PASS (completeness). Print the standard probe banner.

**Gate:** cold prove/verify/proof-size ×3, diffed against the baseline table
above; report keccak perm count and `round_log_size` before/after (expect
37 → ~57–69 perms, round rows 2^10 → 2^11). Numbers named:
`unlink_spike_mu_prove_ms`, `_verify_ms`, `_proof_bytes`.

### WO-U0b [agent-ready] — Keccak service scaling spike (Phase-2 dominant term)

**What:** Measure prover cost of +165 permutations (ExpandA ~150 + tr ~15)
without designing the rejection sampler.

**How:** In a spike example (`unlink_spike_keccak.rs`), enqueue ~165 additional
dummy sponge jobs into the keccak service on top of the normal mdoc proof
(SHAKE-128-shaped: 34-byte absorb, 5 squeeze blocks each — see
`stwo-keccak/src/sponge.rs:12` for the `n_perms = n_absorb + n_squeeze − 1`
accounting). Their outputs may be yielded to a throwaway relation consumed by a
trivial spike component; do not touch production components.

**Gate:** cold prove ×3 and proof bytes at 37, ~100, and ~202 total perms
(three data points, so scaling shape is visible). Numbers:
`keccak_scale_{37,100,202}_prove_ms`, `_proof_bytes`.

**STOP/GO:** After U0a+U0b, main loop decides whether Phase-1/2 estimates hold
(gate: U0a prove ≤ 1.2 s cold, U0b @202 ≤ +700 ms over baseline). If blown,
re-plan before any Phase-1 code.

---

## Phase 1 — private MSO

### WO-U1 [agent-ready, after U0a] — production private-message issuer leg

**What:** Make U0a's flip production: issuer instance private-message in
`prove_mdoc_circuit`, MSO/Sig_structure removed from the public statement,
transcript, and envelope.

**Files/anchors:** mdoc.rs:4342 (issuer instance), statement.rs:1332-1350
(`hosted_public`), statement.rs:322-348 (public mixing — issuer message bytes
must NO LONGER be mixed; mix length + nothing else, mirroring the
private-message mode at :341), envelope structs in sdk/src/lib.rs:854-860 and
`MdocCircuitStatement` serialization (the Sig_structure / MSO fields leave the
statement or become `#[serde(skip)]` witness-side).

**Constraint:** verifier must still terminate with the SAME public API
(`verify_identity(envelope, expected...)`); everything it used to read from
the public MSO is now unavailable — WO-U2 provides the in-circuit
replacements; U1 and U2 land together on one branch, gates run at the pair
level.

### WO-U2 [design-first → then agent-ready] — in-circuit MSO fact re-hosting

**What:** Re-establish, in-circuit, every fact the verifier currently checks
natively on the public MSO (`mldsa_public_mso_facts`, mdoc.rs:1466-1511):

1. **valueDigests membership** — for each disclosed attribute: window-bind
   `digestID‖CBOR-head‖32-byte-digest` at a WITNESS offset into the private
   message byte relation; the digest cell ties to the existing
   `SharedDigestRelation` output of the item SHA (public_digest_bind pattern,
   public_digest_bind.rs:165-181, but the "expected" side now consumes from
   the private byte relation instead of a baked public constant). Per A-729,
   the private digestID is one committed witness/canonical encoding with two
   LogUp consumers: the MSO map key and the IssuerSignedItem `digestID` field
   consume the same cells. The public contract exposes only the maximum
   supported digest-ID value/encoding length.
2. **validity** — bind `validFrom`/`validUntil` byte windows; in-circuit date
   compare against public `today` (reuse the AgeRangeCheck byte-compare
   pattern). Per A-736 there is no serialized validity bit: successful
   verification itself means the private window contained the verifier's
   public `today`.
3. **docType** — window equals public constant.
4. **deviceKey binding** — bind the MSO `deviceKeyInfo` COSE_Key bytes region
   and constrain equality with the (still public, Phase 1) device instance pk
   bytes (ρ‖t1 packed as encoded in the MSO).

**Design decision already made (do not revisit):** window/anchor binds against
the private byte relation, NOT a full `mdoc_cbor_stream` parse of the MSO.
Trust assumption: issuer emits canonical CBOR (issuer is trusted for
credential well-formedness). Document with a `ponytail:` comment naming the
upgrade path (full MSO parse) at each bind site.

**The design-first part (main loop, before delegation):** the existing
`mdoc_window_bind` uses PUBLIC statement offsets; here offsets are WITNESS.
Design the witness-offset bind: consume `(offset+k, expected_byte_k)` pairs
from the position-indexed `FieldBytesRelation` for k in 0..anchor_len with
`offset` a trace cell — anchor bytes preprocessed constants, degree ≤ 2.
Deliverable of the design pass: a one-page constraint spec appended to this
file; only then hand the implementation to an agent.

**Gates:** (a) negative tests, each proven to fail on revert: tampered digest,
wrong digestID, digest bound at a non-digestID position, shifted MSO payload
window, MSO digest mismatch, expired validity, wrong docType, swapped
deviceKey; (b) e2e `product_identity_e2e` + `ts13_e2e` green;
(c) byte-grep regression: NO MSO byte-run, digestID, validFrom timestamp, or
Sig_structure fragment present in the wire envelope (extend the existing
DOB-scrub grep test, sdk/tests/product_identity_e2e.rs:104-114);
(d) measured: `phase1_prove_ms` (cold ×3), `_verify_ms`, `_proof_bytes`,
`phase1_revocation_sha_rows`, and `phase1_revocation_sha_ms` — acceptance
≤ 1.3× U0a spike numbers. A roughly 2.4 KB MSO should be about 38 SHA blocks
and 2.4k SHA rows; materially larger measurements must be explained.

### WO-U3 [agent-ready after A-729 amendment] — remaining statement fingerprint sweep

**What:** Remove every remaining credential-stable value from statement +
envelope.

1. **Moved into U1/U2 by A-729:** digestIDs become a private same-cell witness
   across the MSO-map and IssuerSignedItem surfaces; remove the value from
   public statement serialization, transcript mixing, and tree-0 cache
   material. Retain only a public resource cap.
2. Attribute/value lengths padded to the TS13 buckets
   (`TS13_ALLOWED_REQUESTED_ITEM_PADDED_LENGTHS = [64,128,192]`, ts13.rs:27)
   on the product path too.
3. Per A-736, validity has no serialized output field; assert that no
   timestamp or validity-result field survives serialization. Successful
   verification is the result.
4. Fold in the standing envelope fix: apply the TS13 zeroing projection
   (`MdocMlDsaPublicAuthInput::verifier_input`, mdoc.rs:302-342) to the
   PRODUCT path so raw `c_tilde`/`z`/`hint` never serialize
   (`into_public_view` currently misses `issuer_input`/`device_input`).

**Gate:** a `statement_fingerprint` test that serializes two envelopes from
the SAME credential (different nonces) and one from a DIFFERENT credential
with identical disclosed facts, and asserts the only byte regions that differ
between same-credential runs also differ across credentials (no stable
credential-identifying region). Plus the byte-grep suite. Number:
`phase1_envelope_bytes` (expect ≈ −7 KB from the sig scrub).

### WO-U4 [reduced by A-728] — revocation privacy close-out

**Moved into U1/U2 by A-728:** bind the complete private MSO payload substring
to the issuer-message `FieldBytesRelation`, hash that exact range in the
existing SHA-256 AIR, and feed its private digest through
`MsoDigestBinding::Relation` into `MdocRevocationRangeBind`. Publishing the
MSO digest is forbidden because it would be a credential-stable fingerprint.
The Phase-1 pair owns the wrong-ID, shifted-window, and digest-mismatch
proof-level negatives and the named SHA row/time measurements.

**Remaining gate:** verify the public TS13 statement reveals the epoch and
nothing else about the gap endpoints, and record the anonymity note.

---

## Phase 2 — private device pk (fully-PQ device binding)

**A-733/A-739 scope stop:** Phase 2 is not authorized. The already-created
U5/U7 slices are preserved only on
`parked/unlinkability-phase2-u5-u7`: `0e60a4d3` (U5 ExpandA),
and `81946a21` (U7 hosted private-key hashing). They are **parked, unreviewed
for merge, not authorized** and contribute no Phase-1 progress or acceptance
evidence. A-740 corrected A-739's misclassification of `bf1deb32`: its
constant-width SHA-256 padded-stream/namespace support is mandatory Phase-1
infrastructure under A-728/A-731 and is re-landed with fresh Phase-1
provenance. The Phase-1 delivery contains zero actual Phase-2 files.

Order: U5 → U6/U7 (parallel) → U9. U8 gates the whole phase's perf.

### WO-U5 [design-first] — ExpandA rejection-sampler AIR

30 SHAKE-128 streams (`ρ‖j‖i` absorb, ~5 squeeze blocks each), 3-byte
candidates, 23-bit mask, accept `< q = 8,380,417`, exactly 256 accepts per
stream. Structural template: SampleInBall (sampleinball/mod.rs:889-1302 — the
byte-stream binding at :1028 and the two-sided `≤`/`>` compare at :1004 are
the exact patterns to mirror; the accept/skip FSM replaces Fisher–Yates).
Resource cap: fixed squeeze-block budget per stream with fail-closed
`validate_stream` (mirror MAX_SIB_SQUEEZE_BLOCKS, sampleinball/mod.rs:91);
overflow probability note required in the WO report. Design pass output:
constraint spec + column count + expected log_size, appended here.

#### WO-U5 constraint spec — 2026-07-29 design pass

Status: main-loop reviewed and frozen for implementation. The fixed resource
cap is six SHAKE-128 squeeze blocks per polynomial: five blocks has a
30-stream union-bound overflow probability of `2^-127.485367`, which is
1.43× above a literal proof-wide `2^-128` fail-closed rail. Six blocks reduces
that bound to `2^-542.029992`. The 30 extra permutations relative to the
five-block estimate remain subject to the Phase-2 `≤ 2.0 s` gate.

Protocol order is row-major `poly = i·L+j`, `i=0..5`, `j=0..4`. Job `poly`
absorbs `rho || j || i` and uses the historical stream namespace:
`absorb = stream_base + 16 + 2·poly`, `squeeze = absorb + 1`. Exactly thirty
`Shape::shake128(34, 6, absorb, squeeze)` jobs are appended in that order.
No candidate-count vector, witness-derived preprocessing, or candidate-count
claim is permitted.

`ExpandAAbsorb` has 1,020 active rows (`34·30`) at log 10, scheduled
position-major then polynomial so the 30 copies of each rho byte are adjacent.
Its one base column is `byte`; its public preprocessing columns are
`active, byte_pos, poly, absorb_stream, rho_first, rho_copy, domain_gate,
domain_byte`. It constrains adjacent rho copies, pins positions 32/33 to
`j/i`, and zeros padding. It emits positive
`HashIo(absorb_stream, byte_pos, byte)` tuples and one positive
`RhoCell(byte_pos, byte)` tuple per rho position. U9 consumes each `RhoCell`
negatively.

`ExpandARejection` has 10,080 active rows (`30·336`) at log 14, ordered by
polynomial then candidate. Its twelve base columns are
`b0,b1,b2,low7,top,sample,accept,index,accept_slack[3],reject_delta`; public
preprocessing is
`active,first,last,not_first,poly,candidate,byte_pos,squeeze_stream`.
Define `z=b0+256·b1+65536·low7`, `skip=sample-accept`, and
`a=a0+256·a1+65536·a2`.

- `top`, `sample`, and `accept` are boolean; `accept·(1-sample)=0`;
  `b2=low7+128·top`; `low7` uses Rc7.
- Accepted candidates prove `z+a=q-1`, with `a0,a1` in Rc8 and `a2` in
  Rc7. Rejected sampling candidates prove `z-q=reject_delta`, with
  `reject_delta` in Rc13. Inactive-branch slack is zero.
- The FSM enforces `first·index=0`,
  `not_first·(index-index_prev-accept_prev)=0`, `255-index` in Rc8 on
  sampling rows, `(active-sample)·(index-256)=0`, and
  `last·(index+accept-256)=0`. Thus sampling is the unique prefix, exactly
  256 candidates are accepted, and all remaining cap rows stay done.
- Every one of the six blocks is HashIo-bound even after completion. The
  three squeeze-byte tuples are negative; range uses are positive; each
  accepted coefficient emits positive
  `NttCell(poly,0,index,b0,b1,low7)`, consumed negatively by U6.

The absorb component has two lookup sites, four interaction M31 columns,
direct degree at most two, and bound `log+1`. Rejection has ten sites in
fixed order (three HashIo, low7, count margin, three accept slack,
reject delta, NttCell), twelve interaction M31 columns under batch-four
LogUp, direct degree at most two, and D5 bound `log+2`. No new range tables
are introduced; Rc7/Rc8/Rc13 use the proof-wide range provider. Claim order
is `[absorb_claimed_sum, rejection_claimed_sum]`; log sizes and candidate
counts are verifier-derived and absent from serialization. Both private
claimed sums remain unmasked; A-741 forbids extending the ZK machinery, so
they support no ZK or unlinkability claim.

Module order is
`SharedRangeTable → KeccakService → ExpandAAbsorb → ExpandARejection → U6 → U9`.
U5 reads the Keccak/range handles, draws `RhoCell`, then `NttCell`; U6/U9
consume those handles. A standalone harness may add explicit negative
balancers, but production may not.

The host validator requires 30 canonical streams, whole 168-byte blocks, a
canonical SHAKE prefix, a 256th acceptance within six blocks, and no seventh
block. The AIR consumes the deterministic full six-block stream; a minimal
host witness ending in the block containing the 256th acceptance is expanded
only from that same canonical SHAKE prefix. Overflow and malformed shapes
return typed errors without truncation or panic.

Required positives compare all 30 streams, order, and domain separators with
the FIPS reference and cover `q-1` accepted / `q` rejected. Required
negatives cover wrong stream count, partial/noncanonical/extra blocks,
six-block overflow, rho or `j/i`, stream IDs/positions/bytes, low7/top and
all range boundaries, inverted accept/skip decisions, every FSM boundary,
post-done reactivation, accepted polynomial/index/limbs, service shapes,
claims, and preprocessing. The exploit-shaped self-consistent forged
`A_hat`/U6 witness disconnected from SHAKE must reject. Attack hooks are
snapshotted into evaluator state so negatives remain deterministic under
Rayon.

### WO-U6 [design-first] — witness Â/t̂1 evaluation replacing verifier-native fold

`verifier_native.rs:39-124` currently computes `Â_ij(r,s)`, `t̂1_i(r,s)`,
`q̂(s)` natively and `PublicFoldEval` (statement.rs:683-704) constrains the
fold with those as Eval constants. Replace with: Â coefficients committed
(fed by U5's accepted-coefficient stream via LogUp), t1 coefficients committed
(bound to the MSO deviceKeyInfo bytes from U2's bind), bivariate Horner
accumulators at `(r,s)` — the coeffs pattern (coeffs/mod.rs:659-686) applied
to 30+6 more polynomials. `(r,s)` draw stays post-tree-1-commit
(air-core/src/lib.rs:513-518) — verify the added trees don't move the draw
earlier. Design pass required: digit widths, carry budget (the S5a worksheet
margin argument must be extended to the new terms IN THE REPO, not
out-of-band).

#### WO-U6 domain design — 2026-07-29, pending A-733

Exact current-tree review confirms U5's
`NttCell(poly,0,index,limb0,limb1,limb2)` is the inverse-NTT stage-zero
tuple. Directly feeding those cells to the current fold is unsound. Two
complete constructions are available; Q-733 chooses the authoritative one.

**Audited inverse path (recommended low-risk construction).** U6 lives inside
the existing ML-DSA `Air`, reads U5's shared `NttCell` handle, and reuses the
single post-tree-1 `(r,s)` draw. It must not instantiate a separate Air with
independent challenges. Existing `EvalAtRs` IDs remain 0..29; A uses 30..59
and t1 uses 60..65.

Relation signs are:

| tuple | producer | sign | consumer | sign |
|---|---|---:|---|---:|
| A `NttCell` stage 0 | U5 rejection | + | inverse butterfly | − |
| intermediate `NttCell` | butterfly stage | + | next stage | − |
| A `NttCell` stage 8 | butterfly | + | scaling/Horner | − |
| A/t1 `EvalAtRs` | U6 Horner | − | combined native use | + |
| `T1Cell(i,m,lo9,hi1)` | U6 t1 | + | U9 packed-key decoder | − |

The restored inverse butterfly has 30,720 active rows at log 15, eight
preprocessed, 36 base, and 32 interaction columns. Its range demand is
491,520 Rc8, 245,760 Rc7, and 122,880 Rc13. The A scaling/Horner stack has
7,680 active rows at log 13, five preprocessed, 22 base, and 28 interaction
columns, using 61,440 Rc8, 30,720 Rc7, 30,720 Rc13, and 23,040 Rc9.

The new t1 stack has 1,536 active rows at log 11. Its base is
`lo9,hi1,d0,d1,d2`; it proves `lo9 ∈ Rc9`, boolean `hi1`,
`t1=lo9+512hi1`, and the unique integer equality
`2^13·t1=d0+512d1+512²d2` with every `d+256 ∈ Rc9`. Since
`2^13·1023=q−1`, no field alias exists. Five preprocessed, five base, and
12 interaction columns use 6,144 Rc9 entries. U9 independently reconstructs
the same 10-bit cells from the canonical FIPS five-byte-to-four-coefficient
packing; a byte lookup without boolean split constraints is insufficient.

The private-device serialized eval vector is fixed as
`[coeff 30, A 30, t1 6]`. Component sums are
`[u6_butterfly,u6_A_scaling,u6_t1_horner,coeffs,...]`, with one combined
66-tuple `EvalAtRs` native-use sum last. U5 remains a preceding module with
`[absorb,rejection]`. Base columns enter tree 1; `(r,s)` is drawn only after
that commit; Horner accumulators and lookups enter tree 2. Including current
coeffs, this path commits 460,800 preprocessing, 1,509,376 base, and
1,499,136 interaction M31 cells.

**Clean NTT-domain alternative (smaller, broader protocol refactor).** This
does not retain the coefficient-domain fold. Trim coeffs to z/w/c, publish
canonical stage-zero residues, add canonical scaled-t1 cells, forward-NTT
exactly z[5], c[1], t1[6], and w[6], then enforce for all `(i,k)`:

`Σ_j Ahat[i,j,k]·Zhat[j,k] − Chat[k]·T1hat[i,k] − What[i,k] = q·H`.

Use shared NTT IDs A 0..29, z 30..34, c 35, t1 36..41, and w 42..47.
Final z/c cells have producer multiplicity +6 and six pointwise consumers;
w/t1 use +1/−1. Coeff digits and the existing W/C bindings prove canonical
z/c/w residues. U9's canonical packed decoder binds t1.

The 1,536-row log-11 pointwise component stores 13 three-limb operands,
three balanced base-512 H digits, and four carries: 46 base columns. Its 20
lookups are 13 NttCell, three Rc9, and four Rc13, batching to 20 interaction
M31 columns. The exact quotient range is
`−(q−1) ≤ H ≤ 5q−10`. With radix-256 q limbs `[1,224,127]`, the four carry
ranges are `[-255,1271]`, `[-735,2771]`, `[-1087,3124]`, and
`[-1402,2427]`; adding 4096 places each in Rc13. The largest lifted limb
expression is 1,849,870, below the M31 modulus, and every direct constraint
has degree at most two.

The complete alternative is:

| component | active/log | pre | base | interaction |
|---|---:|---:|---:|---:|
| trimmed z/w/c producer | 1,664/11 | 16 | 26 | 32 |
| scaled-t1 producer | 1,536/11 | 3 | 4 | 8 |
| 18-polynomial forward NTT | 18,432/15 | 8 | 36 | 32 |
| pointwise identity | 1,536/11 | 3 | 46 | 20 |

It commits 307,200 preprocessing, 1,335,296 base, and 1,171,456 interaction
M31 cells, 655,360 fewer than the inverse path. It deletes e/v/carry,
`EvalAtRs`, `(r,s)`, `rho_RLC`, `qhat`, the native-use sum, and
`PublicFoldEval`; leaving any of them as a disconnected/dead trace is
forbidden. Its arithmetic is sound because exact forward NTT is invertible
over `Rq` and every pointwise identity is proven modulo q. This path needs
explicit protocol/worksheet authorization despite its smaller footprint.

### WO-U7 [agent-ready, after U5 spec] — in-circuit tr

`tr = SHAKE256(pk)` over the 1,952-byte private pk: one more private-message
sponge job (~15 perms), pk bytes via the same byte relation that feeds U6's
t1 commitment. Replaces `native_tr` (statement.rs:368-373) for the device
instance only (issuer keeps native tr — its pk stays public).

#### WO-U7 constraint/integration design — 2026-07-29

The existing Keccak service needs no new AIR. Add device-private-key stream
offsets `TR_ABSORB=8` and `TR_SQUEEZE=9`; existing µ, c-tilde, and
SampleInBall offsets remain 10..14, while U5 uses 16..75 under the 128-wide
instance namespace. The device job order is:

1. `SHAKE256(pkEncode)` with `Shape::new(1952,1,b+8,b+9)` — exactly 15
   permutations;
2. `SHAKE256(tr || 0 || 0 || message)` with
   `Shape::new(66+message_len,1,b+10,b+11)`;
3. the existing c-tilde and SampleInBall jobs;
4. U5's 30 row-major SHAKE-128 jobs.

Making `tr` private necessarily rehosts µ as well; this is part of U7, not a
separate protocol choice. The fixed bridge order is
`[pk_tr,tr_mu,mu_ct,w1enc,ct_sib]`. `pk_tr` consumes U9's normalized
`FieldBytes(HOSTED_DEVICE_PK_FIELD_ID=1,k,byte)` and yields the tr absorb
stream. `tr_mu` consumes tr squeeze bytes 0..64 and yields µ absorb positions
0..64. One public-prefix component yields `[0,0] || message` starting at
position 64. Existing µ-to-c-tilde, w1, and c-tilde-to-SIB bridges follow.
Tail sinks consume tr[64..136], µ[64..136], and c-tilde[48..136].

The statement context must distinguish `hosted`, `native_mu`, `private_key`,
and `private_message`; one overloaded `public_message` boolean is
insufficient. Device-private-key mode is `(true,false,true,false)`;
issuer/revocation private-message mode is `(true,false,false,true)`. Only
public-key modes recompute or transcript-mix native `tr`/rho/t1.
Private-key mode mixes an explicit mode tag, public message bytes/length,
namespace, and stream base, but no key or `tr`.

Relative to the current hosted-public device, U7 adds the log-11 pk bridge;
log-6 tr-to-µ and µ-to-c-tilde bridges; and log-7 tr/µ sinks. Exact delta is
10 preprocessing columns/4,864 cells, 10 base columns/4,864 cells, and 32
interaction M31 columns/18,432 cells: 28,160 M31 cells total, with unchanged
maximum log size. Device claimed sums grow from 15 to 20 before U6 changes:
core claims, public suffix prefix, the five bridges, three sinks, then native
use. Claim parsing derives bridge/sink counts from the mode and rejects all
short, long, or swapped vectors.

On the mdoc wire, issuer auth keeps its public key and hides its message;
device auth keeps its public message but serializes an empty public key.
Verifier reconstruction uses zero rho/t1/tr/signature placeholders without
calling `pk_decode` on the empty key. U6/U9 replace every device verifier use
of those values; host device-key checks are removed only after that proof
chain lands. Required regressions cover the 1,952-byte SHAKE reference/KAT,
permutation/job order, every bridge/tail/field-ID/index/stream seam, public
suffix bytes, service and claim shapes, private-key mixing invariance, and an
mdoc round trip whose public bytes contain neither the device key nor `tr`.

### WO-U8 [design-first, engine] — GKR offload of the full permutation chain

NOT for a subagent. Extends the round-function GKR offload
(round_gkr.rs) to keep the ~165 ExpandA/tr permutations' state off the
committed trace. This is fork work (Lucas's stwo dev-copy discipline applies).
Decision gate: only needed if U0b's measured @202-perm number blows the
Phase-2 budget (≤ +700 ms); if the committed-trace cost is tolerable, SKIP
(ponytail: don't build the engine feature the spike says you don't need).

### WO-U9 [agent-ready, after U2] — pk↔MSO binding

Window-bind the private pk bytes (ρ‖t1 as COSE-encoded in deviceKeyInfo)
against the U6 committed t1/ρ cells. Negative: substitute pk ⇒ verify fails.

#### WO-U9 packed-key constraint design — 2026-07-29

Use a dedicated fixed-log-9 `MdocPrivateDeviceKeyBind` with 416 active rows:
32 rho rows followed by 64 five-byte groups for each of the six `t1`
polynomials. The private MSO binder proves only the fixed canonical 35-byte
`deviceKeyInfo`/COSE prefix, keeps the logical window length at 1,987 bytes,
and emits the private public-key start. U9 consumes exactly 1,952 issuer
`FieldBytes` tuples from that start, so removing the public-key constants from
the MSO binder does not change the message-provider multiplicity. Those
source tuples retain the issuer-message field ID and absolute positions. U9
also re-emits the same committed bytes under a dedicated normalized
device-public-key field ID and relative positions `0..1952`; U7 consumes that
single normalized copy into its private `tr` SHAKE-256 absorb stream.

For polynomial `i` and group `g`, let the five packed bytes be
`b0..b4`. Split

`b1=l2+4h6`, `b2=l4+16h4`, and `b3=l6+64h2`,

then derive

`u=[b0+256l2, h6+64l4, h4+16l6, h2+4b4]`.

For each coefficient, prove a private boolean `hi1` and
`lo9=u-512hi1`, range-check `lo9` in Rc9, and emit/consume the canonical
unscaled tuple `T1Cell(i,4g+k,lo9,hi1)`. All five bytes use Rc8 and the six
fragments use Rc7; the reconstruction equations and ranges are
integer-unique below M31. The first 32 key bytes consume issuer bytes and
canonical `RhoCell(pos,byte)` tuples directly.

Relation signs are:

| tuple | producer | sign | U9 sign |
|---|---|---:|---:|
| issuer `FieldBytes` | private message provider | − | + |
| normalized device-pk `FieldBytes` | U9 | − | U7 consumes + |
| `RhoCell(pos,byte)` | U5 | + | − |
| `T1Cell(i,m,lo9,hi1)` | U6 | + | − |
| `MdocDevicePkStart(start)` | private MSO binder | − | + |
| Rc7/Rc8/Rc9 | shared range table | − | + |

The component has 12 preprocessing columns, 16 base columns, and 32 lookup
sites including the claimed-sum blinder after adding five normalized
byte-provider sites. Pair LogUp uses 64 interaction M31 columns plus four for
the blinder counterpart, 68 total. Exact range demand is 1,952 Rc8, 2,304
Rc7, and 1,536 Rc9. Direct constraints are degree at most two and the
framework bound is `log+1`.

The MSO binder removes `device_public_key` from public mixing,
preprocessing, and serialization, reduces its full-key constant window from
63 rows to two prefix rows, and adds the separate private start relation.
U9 claims are `[main_claimed_sum, blinder_counterpart_sum]`. Required
negatives cover every byte lane and fragment, nonboolean high bits, range
boundaries, wrong rho/T1 coordinates, shifted start, forged field ID/index,
tampered preprocessing/claims/prefix, and an end-to-end 1,952-byte key
substitution. Q-733 must preserve the positive canonical unscaled
`T1Cell` producer for either U6 construction.

This U2-start → U9-normalizer → U7 topology is 23,040 committed M31 cells
smaller than making U2 emit each key byte with multiplicity two: it avoids 32
new relation families in U2 and adds only five row-packed provider sites in
U9. The message-provider census reserves one downstream use at each of the
1,952 absolute key positions before it is constructed.

**Phase-2 gate:** fully-PQ private-device-pk proof, negatives (forged Â
coefficient, out-of-range candidate accepted, wrong pk) green;
`phase2_prove_ms` cold ×3 — acceptance ≤ 2.0 s cold desktop.

---

## Phase 3 — out of scope

A-741 supersedes A-737 and rescinds the design-only ZK spike. Do not produce
the four-obligation design or worksheet, request a ZK Math Review, edit the
Stwo proof system, or measure/forward-plan ZK work. Existing shipped partial
measures remain unchanged. The profile stays `ZK=false`, and the delivery
makes no ZK or unlinkability claim.

---

## Reporting

Each WO appends to this file: date, branch/commit, the named numbers, gate
outputs (test names + pass/fail), and any deviation from spec with one-line
rationale. Main loop reviews before the next WO starts.

---

## WO-U0a report — 2026-07-29

Branch/worktree: `codex/unlinkability` from `feat/quantum-safe`
`abf9c27f32bc857f6de7994cfca7ab9372e43baa` (working tree).

Implementation:

- Added the spike-only `unlink_spike_mu` example and doc-hidden prove/fresh
  verify entrypoints. Production wrappers remain hardwired to public-message
  issuer mode.
- Reused the established hosted-test `FieldBytesRelation` provider shape and
  sign convention; device and revocation roles are unchanged.
- The actual fixture issuer Sig_structure is 2,294 bytes. Keccak service shape
  is 37 → 55 permutations and `round_log_size` 10 → 11.

Gates:

- `cargo check -p eu-id-prover --examples`: PASS.
- `RAYON_NUM_THREADS=1 ... unlink_spike_mu`: PASS prove + fresh verify
  (`1,511 ms`, `111 ms`, `2,078,126` raw bytes; correctness-only run).
- `stwo-mldsa --release --test hosted`: PASS.
- `eu-id-prover --release --test mdoc_mldsa
  full_pq_mdoc_proves_and_verifies_with_revocation_end_to_end`: PASS.

Cold 12-thread fresh-process measurements:

| run | `unlink_spike_mu_prove_ms` | `unlink_spike_mu_verify_ms` | `unlink_spike_mu_proof_bytes` | bzip2 wire bytes |
|---:|---:|---:|---:|---:|
| 1 | 696 | 46 | 2,081,246 | 1,728,897 |
| 2 | 692 | 41 | 2,080,158 | 1,716,832 |
| 3 | 674 | 38 | 2,079,326 | 1,717,824 |

Decision: PASS (`max prove = 696 ms ≤ 1.2 s`).

Lifecycle: once U1 made the issuer private-message path unconditional, the
U0a-only entrypoints/example and cache-key mode bit became semantically
identical to production and were removed. The measurements above remain the
gate evidence; the default-off dummy-Keccak probe remains active for service
scaling.

Deviations:

- The required `air-writer` skill was unavailable in the session catalog.
  The spike copies the already-tested degree-≤2 hosted provider instead; every
  new component reports `max_constraint_log_degree_bound = log_size + 1`.
- The work order's 86-byte revocation note is stale at this HEAD; production
  revocation messages are 20 bytes. No revocation behavior was changed.
- Named `*_proof_bytes` is raw bincode proof size; compressed wire size is
  reported separately for comparison with the supplied envelope baseline.

## WO-U0b report — 2026-07-29

Branch/worktree: same as WO-U0a (working tree).

Implementation:

- Added `unlink_spike_keccak --point 37|100|202`.
- Dummy jobs are production-faithful 34-byte SHAKE-128 jobs with five squeeze
  blocks. The middle point is 13 jobs / 102 actual permutations but retains
  the required `keccak_scale_100_*` metric name because the work order asks
  for `~100`.
- A spike-only public-constant HashIo closer batches all absorb/output tuples
  in one degree-≤2 accumulator so the measurement isolates Keccak service
  scaling instead of adding a large unrelated committed trace.

Gates:

- Point 202 one-thread prove + fresh verify: PASS
  (`2,914 ms`, `118 ms`, `1,272,886` raw bytes).
- All nine cold measurements proved and fresh-verified successfully.
- The table supersedes the initial outer-thread-only samples. An intermittent
  point-202 overflow showed that the outer 32 MiB stack did not configure
  unnamed Rayon workers. Both examples now execute inside a named local Rayon
  pool with a 32 MiB stack on every worker; every row explicitly sets
  `RAYON_NUM_THREADS=12` and reports `rayon_worker_stack_bytes=33554432`.

Cold 12-thread fresh-process measurements:

| point (actual) | run | named prove ms | verify ms | named proof bytes | bzip2 wire bytes | round log |
|---:|---:|---:|---:|---:|---:|---:|
| 37 (37) | 1 | 530 | 33 | 1,263,638 | 979,420 | 10 |
| 37 (37) | 2 | 523 | 34 | 1,267,878 | 986,163 | 10 |
| 37 (37) | 3 | 529 | 31 | 1,264,854 | 980,103 | 10 |
| 100 (102) | 1 | 968 | 39 | 1,268,342 | 1,003,253 | 12 |
| 100 (102) | 2 | 960 | 39 | 1,269,350 | 1,004,407 | 12 |
| 100 (102) | 3 | 945 | 38 | 1,268,630 | 1,004,385 | 12 |
| 202 (202) | 1 | 1,544 | 46 | 1,269,670 | 1,004,697 | 13 |
| 202 (202) | 2 | 1,533 | 44 | 1,273,238 | 1,009,008 | 13 |
| 202 (202) | 3 | 1,505 | 44 | 1,270,918 | 1,006,447 | 13 |

Paired point-202 overhead versus point 37 is `+1,014 / +1,010 / +976 ms`.
Decision: **STOP / RE-PLAN** because every sample exceeds the `+700 ms`
Phase-2 budget by `276–314 ms`. WO-U0a passed, but the global rule forbids
starting Phase 1 until this result is replanned.

Post-review hardening:

- Both probes and their AIR plumbing are now compiled only by the default-off
  `eu-id-prover/unlink-spikes` feature. Default production builds keep the
  original inner API shape and exact version-4 tree-0 cache-key encoding.
- Verification now runs against the deserialized Bzip2 round-trip proof.
  U0a also asserts that public-message production verification rejects its
  private-message claim shape; every U0b point asserts that verification with
  a different dummy-job count rejects. The only accepted dummy-job counts are
  the three work-order points: `0`, `13`, and `33`.
- Revalidated after isolation with `RAYON_NUM_THREADS=1`: U0a
  `1,555/110 ms`, 55 permutations, 2,077,534 raw bytes; U0b point 202
  `3,044/121 ms`, 202 permutations, 1,275,590 raw bytes. Both mismatch
  negatives rejected.

U8 replan attribution:

- Point 37→202 adds 10,062,720 Keccak-service cells. The committed
  `keccak_round` base trace accounts for 7,992,320 marginal cells (about
  80%); removing the 201-column boundary wrapper as well adds only 1,498,112
  marginal cells.
- Finer phase timers collected before the stack-safe rerun show that
  committed-cell count is not the immediate
  blocker. The broad `build-components` phase includes the existing
  post-interaction Round-GKR proof: point 37 spends 2.1 ms building its input
  layer, 87.7 ms in `prove_batch`, and 7.6 ms folding coefficients; point 202
  spends 21.0–39.2 ms, 663.9–719.8 ms, and 57.4–60.0 ms respectively. Actual
  component, twiddle, and tie-back generation stays below 1.4 ms at point
  202. The later stack-safe acceptance rerun preserves the same STOP margin.
- The pinned Stwo revision leaves the SIMD GKR layer, sum, eq-evaluation, and
  MLE-fold kernels sequential under the otherwise-enabled `parallel` feature.
  The already-pushed `fork/dev-copy` revision `4f39939e` contains exactly
  those parallel kernels and field-by-field CPU/SIMD proof-parity tests, with
  no verifier or proof-encoding changes. A consumer A/B and conditional repin
  is now the smallest candidate; a new round-transition protocol remains the
  fallback only if that existing engine optimization cannot close the gate.
- A reversible exact-git-pin simulation against pushed
  `4f39939eacd0c5efc8ee157e4215a250ca29168f`, with the original lock graph
  otherwise preserved, passed:

  | point | run 1 prove ms | run 2 prove ms | run 3 prove ms |
  |---:|---:|---:|---:|
  | 37 | 474 | 481 | 463 |
  | 100 (102 actual) | 724 | 744 | 719 |
  | 202 | 997 | 966 | 968 |

  Paired point-202 overhead is `+523 / +485 / +505 ms`, clearing the
  `+700 ms` hard gate in every sample. Point 202 at one worker is
  2,877–3,002 ms versus 2,914 ms on the old pin; exact-pin U0a is
  548–594 ms. The eu-id encoded seeded-GKR equality test plus Stwo's
  serial/parallel CPU/SIMD proof-parity and stable proof/artifact-digest tests
  all pass. Two earlier middle-point diagnostics coincided with obvious
  host-wide contention (`1,791/1,885 ms`, verify `130/107 ms`, fresh tree 0
  `107/68 ms`, versus the clean trio's verify `40–42 ms` and tree 0
  `20–21 ms`) and are retained as contaminated diagnostics, not gate samples.
  After measurement all four production pins and the lockfile were restored
  unchanged.
- Watched mailbox question
  `tasks/q10-wo-specs/mailbox/inbox/Q-727-unlinkability-u0-stop-go.md` asks
  for authorization to repin all four Stwo-family dependencies to that exact
  already-pushed candidate. If authorized, the measured committed-trace cost
  is tolerable and full permutation-chain U8 is skipped per its own decision
  gate. No Phase-1 work starts before the `A-727` answer. Three consecutive
  goal turns, including two bounded outbox watches and final direct checks,
  found no `A-727`; the implementation is therefore paused at this explicit
  external-authorization boundary with the production pins restored.

## WO-U0 post-repin acceptance — 2026-07-29

Authorization and landing:

- Mailbox answer `A-727-unlinkability-u0-stop-go.md` authorized the exact
  four-family repin to
  `4f39939eacd0c5efc8ee157e4215a250ca29168f` and declared Phase 1 GO after
  post-repin acceptance.
- Isolated commit `821d8c7d967043678d0c7486a40377937d0b06bc` changes only
  `Cargo.toml` and the four matching Stwo-family `Cargo.lock` source entries.
  No transitive package, `hashbrown`, verifier, or proof-encoding change is
  present.
- The commit message records the authorized ancestry:
  `99d73f3a` order-preserving cross-instance parallelism, `9c5bebf1`
  example-only glue, `cb95b17b` inline packed-field arithmetic, and
  `4f39939e` parallel GKR/MLE kernels plus parity tests. The measured
  justification is old-pin `37→202 = +1,004 ms` average versus candidate
  `+504 ms` average.

Post-repin test gates (`RAYON_NUM_THREADS=1`,
`RUST_MIN_STACK=536870912`, release, serial test harness):

- Full default workspace: PASS, 470 passed / 18 ignored / 37 suites.
- Full `eu-id-prover/unlink-spikes` workspace: PASS, 472 passed /
  18 ignored / 37 suites.
- All ignored workspace gates: PASS, 18 passed / 470 filtered.
- Consumer seeded encoded-GKR equality: PASS, 1 passed.
- Exact-SHA upstream CPU/SIMD GKR+MLE parity group: PASS, 10 passed.
- Stable proof/artifact digest: PASS once with serial `prover` and once with
  `prover,parallel`; both matched the pinned digest.
- The 512 MiB test-stack setting is intentional for the hosted ML-DSA proof
  suites. A diagnostic default-stack run reproduced the known
  `mdoc_mldsa` 2 MiB worker-stack overflow; the spike runner's named Rayon
  pool independently retains 32 MiB on every worker and prints that
  provenance on every measurement.

Cold post-repin U0b acceptance (12 workers, each row a fresh process):

| pair | point-37 prove / verify / tree-0 ms | point-202 prove / verify / tree-0 ms | paired overhead |
|---:|---:|---:|---:|
| 1 | 470 / 33 / 17 | 932 / 45 / 18 | +462 ms |
| 2 | 463 / 32 / 17 | 1,008 / 47 / 19 | +545 ms |
| 3 | 468 / 33 / 17 | 939 / 46 / 19 | +471 ms |

All three are clean and below the `+700 ms` gate. The one-worker point-202
confirmation is 2,853 ms prove / 116 ms verify / 1,275,270 raw proof bytes,
within noise of the old-pin 2,914 ms prove result and therefore shows no
serial regression.

Cold post-repin U0a acceptance (12 workers, fresh processes):

| run | prove ms | verify ms | raw proof bytes | bzip2 wire bytes |
|---:|---:|---:|---:|---:|
| 1 | 542 | 38 | 2,078,078 | 1,705,120 |
| 2 | 561 | 42 | 2,079,614 | 1,709,176 |
| 3 | 607 | 40 | 2,077,486 | 1,699,979 |

Every run is below the `1.2 s` rail and executes the production-mode mismatch
negative after fresh verification.

Demo-baseline guard (no Rayon override, one cold iteration per fresh process):

| path | prove ms ×3 | fresh verify ms ×3 | wire/envelope bytes ×3 |
|---|---|---|---|
| product `identity_probe` | 507 / 511 / 513 | 74 / 74 / 80 | 956,456 / 948,610 / 948,514 |
| TS13 `pq_perf_probe` | 500 / 490 / 487 | 37 / 34 / 38 | 977,120 / 983,218 / 984,386 |

The product probe reported both `dob_cbor_in_envelope=false` and
`dob_ascii_in_envelope=false` in all three processes. Both paths materially
improve prove time; the post-repin numbers at the top of this file are now
the externally quoted baseline.

Decision: **U0a PASS, U0b PASS, repin PASS, Phase 1 GO.** WO-U8 remains
skipped under its own gate unless a later Phase-2 measurement reactivates it.
The earlier contention-tainted 1,791/1,885 ms middle-point diagnostics remain
recorded above and excluded with their elevated verify/tree-0 evidence.

## WO-U2 witness-offset constraint spec — 2026-07-29 design pass

Status: approved by A-731 after A-728/A-729/A-730 resolved the sequencing and
compatibility cuts. The additive A-731 gates below are part of the approved
implementation. Exact-HEAD compatibility review subsequently proved that the
accepted profile permits additional `valueDigests` namespaces; Q-732 asks for
the exact compatible bounded-scan completion instead of silently narrowing
the profile to one namespace.

### Public shape and private witness

- Public, bounded before allocation: issuer message length (≤ 4,160), MSO
  payload length (≤ 4,096), attribute count (≤ 4), public `docType`, Phase-1 device
  ML-DSA public key and policy date. Per A-736, no `valid_today` field is
  serialized; verification success is the assertion.
- Prover-only and skipped by serialization: issuer Sig_structure bytes, MSO
  bytes, the Sig_structure payload-anchor offset, every MSO-relative window
  offset, dates, digest-entry metadata, and (subject to Q-729) digest IDs.
- The payload anchor is the canonical empty external-AAD byte followed by the
  canonical CBOR byte-string head for the public MSO length. Its witness
  position fixes `mso_start = payload_anchor_offset + anchor_len`. Every fact
  offset is represented relative to that same `mso_start`, not as an
  independent absolute pointer.

All public lengths are checked against named caps before constructing a
`Vec`, a SHA layout, a tree-0 key, or a verifier module. Zero lengths,
overflowing `offset + len`, and unsupported buckets return typed errors.

### Shared private-message provider

One committed row-wise provider replaces U0a's public-constant spike provider.
For message position `i`, its active row commits `byte_i` and an
`extra_uses_i` multiplicity, and emits

`-(1 + extra_uses_i) / combine(HOSTED_MSG_FIELD_ID, i, byte_i)`.

The private issuer ML-DSA bridge consumes one positive copy of every row.
WO-U2 windows and the MSO-payload bridge consume the remaining positive
copies. LogUp therefore forces `extra_uses_i` to equal the actual number of
additional consumers; it is not a host assertion and needs no range table,
matching the repository's existing committed lookup-table multiplicity
pattern. A wrong provider byte, index, or count leaves a non-zero global
claimed sum. Inactive byte cells are fresh; the row count is
`next_power_of_two(message_len + 256)` and the public transcript mixes only
that length/shape. The provider and its claimed-sum blinder publish
proof-carried claims; verifier construction never receives the bytes or
multiplicities.

Provider constraints:

| constraint / relation | degree |
|---|---:|
| active/index selectors are canonical preprocessed columns | 0 |
| inactive relation numerator = 0 through the active selector | 2 |
| `FieldBytesRelation` entry with numerator `-active·(1+extra_uses)` | 2 |
| claimed-sum blinder entry/counterpart | 2 |

### Chunked witness-offset binder

`MdocPrivateMsoBind` uses a fixed log-9 domain and 32 byte columns per active
row. A logical window occupies one or more consecutive chunks. Each row
commits the common payload-anchor offset, the window's MSO-relative offset,
and up to 32 bytes. Preprocessed columns pin row kind, chunk-relative index,
byte enables, public expected bytes, and continuation markers.

For byte `k` in a chunk at public relative index `r`, the component consumes

`(HOSTED_MSG_FIELD_ID,
  payload_anchor_offset + payload_anchor_len + window_offset + r + k,
  byte_k)`.

The first payload-anchor row instead consumes its public canonical bytes at
`payload_anchor_offset + k`. A global continuation selector forces the payload
anchor offset equal across every active payload/fact row; a separate
same-window selector forces each logical window offset equal across its
chunks. Thirteen-bit decompositions constrain the payload-anchor offset,
`issuer_message_len - payload_anchor_offset - payload_anchor_len - mso_len`,
each `window_offset`, and `mso_len - window_offset - window_len`. Thus the
complete payload lies inside the bounded private issuer message, every fact
window lies inside that one payload, and M31 wraparound cannot redirect
either. Relation membership independently requires every resulting absolute
position to exist.

Witness bits are boolean on every row, including inactive rows; inactive
offset bits are sampled as fresh random bits, while inactive date/time digit
bits encode fresh random valid digits so the global `digit ≤ 9` constraints
remain satisfiable. Booleanity and digit bounds are therefore degree 2 without
multiplying by an active selector. Only linear recomposition/range equations
are active-gated, keeping them degree 2.

Core constraints:

| constraint | gate | degree |
|---|---|---:|
| active / row-kind / byte-enable selectors are canonical preprocessing | — | 0 |
| offset, range-slack, and validity witness bits are globally boolean | — | 2 |
| common payload-anchor and same-window offset transitions | continuation selector | 2 |
| payload/window offset and slack recompositions | corresponding start selector | 2 |
| constant byte equals preprocessed expected byte | constant byte selector | 2 |
| issuer-message `FieldBytesRelation` lookup at witness position | byte selector | 2 |
| 32-byte item `DigestBytesRelation` lookup | attribute digest-row selector | 2 |
| MSO-SHA field lookup at public padded-stream index | payload-mirror selector | 2 |
| claimed-sum blinder entry/counterpart | all rows | 2 |

The corrected main-binder maximum schedule is: 130 padded-payload chunks
(4,096 raw MSO bytes plus at most 64 bytes of canonical SHA-256 padding), 63
chunks for the complete 1,987-byte canonical Phase-1 device-key outer run,
three or four validity chunks, one docType chunk, one payload-anchor row, and
two profile-constant chunks: 200–201 active rows. Digest-map walking is moved
to Q-732's separate fixed-log9 scanner rather than squeezed into this binder.
The implementation must record both exact final censuses rather than relying
on the earlier 206-row estimate.

### Fact rows

1. **valueDigests:** A-729 requires the canonical uint digest ID to be one
   bounded private witness/canonical encoding whose committed cells have two
   LogUp consumers: the MSO `valueDigests` key and the IssuerSignedItem
   `digestID` field. Independent witnesses on the two surfaces are forbidden.
   Only a maximum supported ID/encoding-length cap is public. Exact-HEAD
   review proves a local digest-entry anchor and a single-namespace prefix are
   both insufficient for the currently accepted multi-namespace profile.
   Q-732 therefore proposes a separate fixed-log9 bounded scan with
   `1 + namespace_count + digest_entry_count ≤ 256`: it walks definite map
   counts, proves exactly one public requested namespace, binds each selected
   digest to its item SHA relation, and rejects all duplicate IDs using a
   private multiset against a strictly increasing sorted-ID track. The scan
   and main binder share the same private `mso_start` relation.
2. **validity:** canonical `validFrom` and `validUntil` label/tag/text-head
   anchors are followed by the complete private 20-byte tdate strings. The
   restored syntax, digit, month/day/hour/minute/second range, UTC suffix, and
   23-bit date-key slack constraints preserve every check currently performed
   by `mldsa_public_mso_facts` and prove
   `validFrom ≤ today ≤ validUntil`; there is no serialized validity output.
3. **docType:** a canonical `"docType"` key plus text value run equals the
   public statement constant.
4. **deviceKey:** the complete canonical
   `deviceKeyInfo.deviceKey` ML-DSA COSE_Key run—including map labels, kty,
   alg, byte-string head, and all 1,952 `pkEncode` bytes—equals the still-public
   Phase-1 device instance key.
5. **profile constants:** canonical MSO `version` and
   `digestAlgorithm = "SHA-256"` key/value runs are bound to their supported
   constants. Removing the public MSO parser must not silently drop either
   rejection currently enforced by `mldsa_public_mso_facts`.

The old `PublicDigestBind` is removed when this private binder lands, so every
item SHA digest has exactly one positive consumer.

Each bind site carries the required `ponytail:` upgrade note: a future
non-canonical-issuer profile must replace that anchor with a full private MSO
CBOR parse; this WO intentionally relies on the trusted issuer's canonical
encoding.

### A-732 scanner ruling — exact audit resolved

Current `parse_mso_value` semantically matches only the requested text
namespace. Every nonmatching outer key and value may be arbitrary
Ciborium-accepted CBOR, including nontext keys, indefinite or nonminimal
encodings, tags, floats, and nested containers. The existing
`MdocCborStream` is not an exact replacement: it has depth 8, definite/minimal
container rules, a smaller simple-value language, and no UTF-8 validation.

The narrow scanner is authorized by A-732: the compatibility cut requires a
definite outer map with canonical definite text keys and definite canonical
`uint -> bstr32` values for every namespace. It uses the fixed-log-9
`HEAD,(NS,DIGEST*)*,INACTIVE` schedule, a private cursor/count state machine,
exact requested-namespace match count one, per-attribute ID/digest selectors,
and a raw-ID multiset against a strictly increasing private sorted track.
For four attributes its frozen census is four preprocessing columns, 324
trace columns, 51 main relation sites, and 108 interaction M31 columns
including the blinder counterpart.

The rejected exact-compatibility alternative needs a fixed-log-13
Ciborium-language parser
pipeline. It normalizes direct-map versus tag-24/bstr MSO roots, fully parses
and skips arbitrary nonrequested subtrees, validates segmented text/UTF-8,
and emits compact descriptors only for the direct top-level `valueDigests`,
its semantic namespaces, and canonical requested digest entries. The
fixed-log-9 semantic scanner consumes those descriptors and performs the same
ID/digest/duplicate checks. Its complete frozen reference design has two
1,900-column parsers plus envelope/scope/UTF-8 components: 4,138 trace
columns, 120 interaction M31 columns, and 12 claims/components for four
attributes. This construction is sound but likely fails the Phase-1
performance rail; it must not be silently replaced by the narrower existing
parser.

For either path A-734's zero-site chain is
`MdocMsoStart(mso_start,is_v2)` from binder to scanner and
`MdocPrivateDigestId(enc_len,b0..b4,id_lo16,id_hi16,is_v2)` from item to
scanner. The scanner binds the item SHA digest, keeps `is_v2` constant, and
returns an exact issuer-position use census that is checked-added to the main
binder census before the private message provider is constructed.

### Minimal U4 bridge requested in Q-728

The current generic multi-window SHA exposure would allocate one relation
site per MSO byte and is not acceptable at the 4,096-byte MSO cap. Extend the
existing SHA field-exposure machinery with a full-padded-stream mode: all 64
message bytes are derived linearly from the already-constrained `W` bit
planes, one public block-counter trace column indexes the block, and 64 fixed
`(field_id, block_counter·64+k, byte_k)` relation sites operate row-wise
across blocks. Do not add 64 byte trace columns or duplicate Range8 sites.
The binder consumes every padded-stream tuple. Raw
positions additionally consume the private issuer-message relation at the
payload witness offset; padding positions are pinned to canonical
`0x80 || 0* || bit_len`. This keeps interaction width constant instead of
O(MSO bytes), while the existing SHA constraints and final-block schedule
produce the digest. Its `SharedDigestRelation` feeds
`MsoDigestBinding::Relation`.
The expected added SHA layout is one trace column and 64 field-yield sites;
with the existing 58 service sites plus one digest site, 123 total sites batch
to 31 QM31 / 124 M31 interaction columns at log 13 (about 1.02 million
marginal interaction cells). If implementation needs committed byte columns
or duplicate range sites, stop and re-price the roughly doubled marginal
cost before landing it.
`MdocRevocationRangeBind` must decouple digest source from revocation-message
direction: the digest is consumed positively from the MSO SHA relation while
the 20-byte hosted revocation message is still provided negatively under
`HOSTED_MSG_FIELD_ID`. Reusing the legacy Relation-mode field ID/direction
would be unbalanced and is forbidden.

### Frozen relation polarity and component order

The implementation must preserve this table in a doc comment next to the
assembled Phase-1 components:

| relation / handle | emitter | sign | consumer(s) | sign |
|---|---|---:|---|---:|
| issuer `HOSTED_MSG_FIELD_ID` tuple at position `i` | private message provider, multiplicity `1+q_i` | − | issuer ML-DSA µ absorb once, plus every U2/raw-MSO read counted by `q_i` | + |
| MSO-SHA padded-stream field tuple | separate MSO SHA, once per padded byte | − | private MSO binder, exhaustively over the padded stream | + |
| each item SHA `SharedDigestRelation` / resolved `DigestBytesRelation` | item SHA final block | − | private MSO binder, exactly once | + |
| MSO SHA `SharedDigestRelation` / resolved `DigestBytesRelation` | MSO SHA final block | − | revocation range digest bind, exactly once | + |
| revocation `HOSTED_MSG_FIELD_ID` tuple | revocation range for all 20 bytes | − | revocation ML-DSA µ absorb | + |

The private issuer provider equation at every position is therefore
`-(1+q_i) + 1 + q_i = 0`. The revocation relation-mode path must not reuse the
legacy positive field-ID-41 message entries.

Module/draw order is frozen as: SHA/range tables; Keccak service; private
issuer-message provider; issuer ML-DSA; device ML-DSA; attribute SHA and,
only for revocation-bearing TS13 proofs, a separate MSO SHA; private MSO
binder; validity logic if separate; revocation range; revocation ML-DSA;
remaining predicates. Product proofs must not instantiate the MSO SHA.

Within the binder, interaction sites are frozen as: 32 issuer-message queries,
32 padded-MSO-stream queries, four item-digest queries, then the claimed-sum
blinder last; its blinder-counterpart component immediately follows the main
component. Unused sites have zero numerator.

### Transcript, cache, and required evidence

Prover and verifier construct the same module/claim order and private issuer
claim shape. The transcript mixes only public lengths and resource caps, row
schedule, preprocessed fingerprints, public constants, and relation
shapes—never message bytes, offsets, dates, multiplicities, or private digest
IDs. The
tree-0 key includes those same verifier-known determinants and the provider,
binder, and MSO-SHA log/column shapes; it excludes every witness value.
Every preprocessed column—including active/index columns, continuation
markers, expected anchor constants, and row schedule—is a function of public
shape/policy/caps only. Two different credentials with identical public shape
must have byte-identical tree-0 roots.

Required proof-level negatives are: provider-byte mismatch; `extra_uses ± 1`
including overlapping windows; missing/extra provider claims; a later fact
row with a different payload-anchor offset; a continuation chunk with a
different window offset; payload/window wrap and out-of-bounds; wrong payload
anchor; digest mismatch and a digest at a non-digest position; wrong namespace
and duplicate digest ID; unsupported version and non-SHA-256 algorithm;
expired/not-yet-valid plus inclusive-boundary dates; malformed tdate syntax,
`24:00:00`, and missing `Z`; wrong docType; swapped device key plus altered
kty, alg, and byte-string length; raw-MSO mirror mismatch; SHA padding marker,
zero, and bit-length mutations; MSO-digest/revocation-ID mismatch; zero and
over-cap message/MSO lengths; and short/long private issuer claim vectors.
The honest payload-offset fixture must assert there is no second anchor
occurrence, then shift `mso_start` to a position without anchor bytes and
obtain proof-level rejection. The µ-consumer totality regression must pin that
the private issuer ML-DSA absorb consumes every index
`0..issuer_message_len`, not merely the queried windows.
Serialization gates must prove that the public statement round-trips and
verifies while containing no issuer Sig_structure/MSO run, validity timestamp,
duplicate private `deviceKeyInfo.deviceKey` COSE wrapper/run, or
credential-selected digest entry. The 1,952-byte raw Phase-1 device public key
remains a required serialized public input. Fresh and memoized tree-0 roots
must agree, failed verification must not populate the cache, and product
proofs must not instantiate the U4 MSO SHA.

### Resolved integration rulings — 2026-07-29

- A-732 selects the 324-column fixed-log-9 canonical multi-namespace
  `valueDigests` scanner and rejects the 4,138-column Ciborium-compatible
  bundle. The cut must return typed errors and pass every available real
  vector, including demo output with extra namespaces.
- A-734 selects the zero-site binder → scanner → item chain. The private
  `is_v2` bit rides in the same `(mso_start,is_v2)` and selected-digest tuples,
  is boolean/constant at every active prefix, and conditionally enforces v2
  key order without entering public material.
- A-735 selects full fixed-shape private predicate normalization while
  preserving the wide accepted value language. The celes 2.8.2 mapping
  (250 rows plus XK) is pinned in a log-9 tagged table; all date encodings and
  nationality scalar/array encodings share one maximal public shape.
- A-736 selects the exact two-entry Phase-1 stable-region whitelist (device
  public key, removed by U7/U9; issuer trust key, permanently public), forbids
  a serialized `valid_today` field, and requires an ignored empty-whitelist
  Phase-2 gate now.
- A-733 defers all Phase-2 implementation. The inverse-NTT path is
  presumptively dead, the old 1–1.5 s estimate is invalid, and a future clean
  NTT path must first ship a new integer-lift/pointwise worksheet while
  preserving the canonical unscaled coefficient-domain `T1Cell` producer.
- A-741 supersedes A-737 and removes Phase 3/ZK entirely from scope. No
  design, worksheet, Math Review, fork edit, measurement, or forward plan is
  authorized; `ZK=false` and the no-unlinkability-claim boundary remain.
- A-738 authorizes minimal/definite/exact product IssuerSignedItem tokens and
  no trailing data while preserving v1 key order and value forms. Rejection
  is typed with token+offset, the outer tag-24 length assumption is bounded,
  and every available real item vector must pass.

### A-735 fixed-shape predicate-normalization design

The public item contract is reduced to three request modes:
`ValueEquality`, `BirthDate`, and `Nationality`.  The private witness carries
the padded item plus an optional selected nationality-member index.  No
birth-date encoding, nationality encoding, scalar/array selector, member
count, selected index, or private MSO version is mixed into the transcript or
tree-zero material.  All request modes pay the same maximal private-item
shape.

Starting from A-734's 110-column item trace, normalization adds 44 trace
columns: one normalized output byte; one nationality member count; three
`count - 1` bits; one selected-text selector; two ASCII case-fold bits; 32
date-digit bits; and four country-lookup payload cells
`(num_hi,num_lo,upper0,upper1)`.  The final item trace is 154 columns.
Nationality adds one logical country lookup before the final claimed-sum
blinder (55 to 56 sites), which still occupies 28 paired secure columns; the
counterpart keeps the total item interaction width at 116 M31 columns.
Booleanity is global and every remaining identity is linear or
selector-times-linear, so the `log N + 2` degree bound and coefficient
retention remain unchanged.

Birth-date mode privately selects canonical packed `bstr(4)`, direct
`tstr(10)`, or tag-1004 `tstr(10)`.  Text digits and separators are proved,
then every form emits exactly four normalized bytes
`(year_hi,year_lo,month,day)`.  Product composition therefore always uses the
packed DOB predicate binding.

Nationality mode privately selects a scalar or canonical definite array of
one through eight canonical two-byte bstr/tstr members.  A running count
proves the declared array cardinality; a one-hot proven member header carries
the private selection.  Numeric members pass any u16 through and consume the
dummy country tuple.  Text members prove two ASCII lowercase-fold bits,
consume their real country tuple, and emit the mapped numeric u16.  Product
composition therefore always uses the numeric nationality predicate and the
numeric accepted set is the only public policy table.

The country relation is the arity-five tuple
`(tag,num_hi,num_lo,upper0,upper1)` on a fixed log-9 table.  Row zero is the
active numeric dummy `(0,0,0,0,0)`.  Rows 1 through 250 are the exact
`celes = 2.8.2` `Country::get_countries()` order with tag one; that 250-entry
array already includes unique XK/383, so XK is asserted explicitly rather
than appended as a 251st country.  Rows 251 through 511 are inactive,
deterministically masked preprocessing.  One multiplicity trace column
provides negative tuples; each nationality item consumes one positive tuple.
The exact table rows, golden digest, celes pin, and XK uniqueness are v10
determinants.

The exact marginal census is 22,528 item trace cells at log 9 or 45,056 at
log 10, plus 5,632 cells for one shared country table.  Thus a log-9
nationality item adds 28,160 committed cells and a log-10 item adds 50,688.
The measured gate is named `u3_normalization_prove_ms`.

The proof-level negative matrix covers private-form flips, date
digit/decomposition/output mutations, wrong alpha-2 mappings, array
cardinality and selection faults, numeric/real-row and alpha/dummy-row swaps,
unknown alpha-2 values, and country multiplicity/claimed-sum faults.  The
equal-shape gate covers all three date forms, numeric and case-varied alpha-2
scalars, arrays of every length 1 through 8 with varying selections and mixed
member encodings, plus the A-734 v1/v2 pair.  Within one request mode and
bucket, serialized public statements, module layouts, public transcript
prefixes, and fresh tree-zero roots must be byte-identical.

### Phase-3 Math Review checkpoint — 2026-07-29

The exact-pin read-only review found that adding random dummy rows to private
trace columns is necessary but not sufficient. Stwo separately commits and
opens midpoint coefficient-split composition parts, exposes direct committed
tree queries, folds batched evaluation quotients together with query siblings,
and reveals the final FRI layer. The existing synthetic monomial Vandermonde
test is not a rank proof for that actual Circle disclosure matrix.

The review therefore requires four independently justified mechanisms before
the profile may advertise zero knowledge: full-field dummy-row interpolation
with an exact Circle-matrix rank argument; randomized composition/quotient
decomposition preserving the recursive Circle basis and its one-dimensional
FFT-space gap; an independent BSCR mask oracle committed before the PCS
batching challenge and integrated into mixed-domain Circle FRI; and a tree-1
pre-beta mask for every witness-dependent claimed-sum slot. These obligations
follow Circle STARKs section 5.4 and Haböck--Al Kindi ePrint 2024/1037
Protocol 2; the published monomial/Lagrange quotient construction cannot be
ported mechanically to the exact Stwo basis.

A-741 later superseded A-737 and rescinded this design-only work. The review
above is retained solely as historical rationale for keeping
`zero_knowledge=false`; it is not an active design plan. No Stwo proof-system
change, ZK review, measurement, or unlinkability claim is authorized.

### WO-U7 core implementation checkpoint — 2026-07-29

Commit: `81946a21`.

`stwo-mldsa::statement` now has a hosted public-message/private-public-key
mode. It consumes normalized `pkEncode` bytes from proof-wide
`FieldBytesRelation` field id 1, proves four ordered Keccak service jobs
(`tr`, µ, c-tilde, SIB), bridges `pk→tr→µ→c-tilde`, consumes all three
squeeze tails, and excludes `rho`, `t1`, and derived `tr` from public
transcript mixing. Its exact public API exposes four job shapes, a 20-claim
count, and the committed layout. Legacy hosted modes and their public mix are
unchanged.

The core intentionally retains one temporary Phase-2 boundary: the folded
ML-DSA identity still reads compatibility `rho/t1` values until U6/U9 replace
that native evaluation. Tests therefore include both a changed field-id-1
provider and a self-consistent replacement of provider bytes plus compatibility
`rho/t1`; both reject. Additional coverage pins the SHAKE KAT, precise
`+10/+10/+32` column and `+4,864/+4,864/+18,432` M31-cell deltas, key-independent
public mix, wrong field id, public-message mutation, claimed-sum mutation, and
missing `tr`/µ service shapes.

Independent gates pass with the campaign's one-worker policy:
`RAYON_NUM_THREADS=1 cargo test -p stwo-mldsa --release --test hosted
-- --test-threads=1` reports 16/16, including every new private-key test;
the full crate release suite reports 125 passed and 3 ignored; scoped
warnings-denied Clippy, workspace formatting, and `git diff --check` pass.
Running the hosted test binary with unconstrained default Rayon and concurrent
test threads exhausted a worker stack; the specified one-worker command
passes without increasing `RUST_MIN_STACK`.

The independent review's verifier-safety blocker is closed. Only the new
hosted-private-key verifier constructor returns `Result`; it validates the
exact group-evaluation and 20-claim vector lengths before reaching the legacy
`Claims::from_flat` panic boundary. Short and long vectors for both shapes,
plus a same-length reordered vector, now return `InvalidStructure` without
panicking. Hosted-private-key inputs retain a zero `tr` placeholder (the
actual value exists only inside the private Keccak service witness), and
proof-level mutations of every bridge/sink claim at indices 11 through 18
reject. Legacy constructors and transcript encodings remain unchanged.

### Phase-1 standalone SHA namespace checkpoint — 2026-07-29

Commit: `362743af` (fresh Phase-1 provenance after A-740 corrected
`bf1deb32`'s A-739 misclassification).

The conditional log-13 MSO SHA instance now uses the fixed
`mdoc/mso-sha` consumer namespace on both prover and verifier. Empty namespace
remains byte-for-byte compatible: all 14 legacy preprocessing IDs and the
transcript draw are unchanged. A nonempty namespace is encoded injectively as
its byte length plus lowercase hexadecimal bytes; only the ten consumer-read
columns (`is_first_row` and the nine round-cyclic columns) are renamed.
Shared SHA tables and their range providers deliberately retain their global
IDs, so the standalone and merged consumers continue to deduplicate them.

Canonical tree-zero reconstruction uses the same namespaced generator on both
sides and is witness-independent. A namespaced standalone consumer at log 13
now composes with the smaller merged consumer, while leaving both unnamespaced
still fails closed on the legacy `sha256_k_lo` collision. The full
`stwo-sha256` release suite reports 165 passed and 18 ignored; the dedicated
namespace, default-compatibility, collision, canonical-root, and real-proof
gates pass. Independent review found no P0–P3 issue. The revocation mdoc
round trip now completes proving and reaches only the separately tracked
public-statement projection rejection, confirming that the preprocessing
collision itself is closed.

The same checkpoint carries A-728's constant-width full-padded stream:
one block counter and 64 row-wise W-bit-derived relation sites, with no byte
columns, per-block selectors, or duplicate Range8 checks. Fresh compilation
found the historical patch's trace test nested inside `impl Layout`; the test
body was moved unchanged into the existing `cfg(test)` module. The final
fresh-provenance gates are 165 normal + 18 ignored SHA tests, 13 focused
stream tests, six namespace/fail-closed tests, and a clean eu-id-prover check.

### Phase-3 Math Review disposition — 2026-07-29

Historical decision: **NO SIGN-OFF** at Stwo `4f39939e`. A-741 subsequently
removed all Phase-3/ZK design, review, implementation, and measurement work
from scope. Do not modify the proof system or advertise zero knowledge.

The exact implementation independently commits every recursively midpoint-
split composition part (`prover/mod.rs`), discloses each part at OODS
(`core/proof.rs`), batches direct tree openings into FRI
(`prover/pcs/mod.rs`), exposes the rest of each fold-step-two four-point
coset, and serializes last-layer coefficients (`prover/fri.rs`). The current
TS13 rank test is only a synthetic monomial Vandermonde and proves no rank
property of those Circle disclosures.

The review had identified missing evidence across the committed-column
census, Circle disclosure matrix, composition decomposition, FRI masking,
claimed-sum masking, simulator statement, adversarial suite, and cold
measurements. A-741 makes that list historical and non-actionable. The
primary references do not support a QROM/post-quantum
transcript-unlinkability claim.

### WO-U5 independent audit checkpoint — 2026-07-29

Commit: `0e60a4d3`.

Read-only review found no defect in the frozen rejection-sampler equations,
relation tuple order/signs, range multiplicities, six-block consumption, claim
order, or serialization. Focused default tests (10 passed, 1 ignored), the
ignored proof-level adversarial matrix, and the ignored real 180-permutation
Keccak composition test all pass.

The implementation pass closes every standalone audit item. Proof helpers
derive and pin canonical, witness-independent tree-zero roots; a padding-only
preprocessing mutation proves against its attacked tree and then fails with
`PreprocessedRootMismatch` against the canonical root. Public stream bases
and polynomial indices are validated symmetrically by fallible prover and
verifier constructors, with the maximum final stream ID exactly `M31::P-1`.
The AIR now constrains the previously unused polynomial, candidate,
byte-position, and stream schedule metadata.

The expanded host matrix covers short/long/partial/noncanonical streams and
an injected six-block overflow. The proof matrix covers range/comparison/FSM,
copy, padding, preprocessing, stream, claim, and self-consistent forged-rho
attacks; the real-service matrix covers 3/5/7 blocks, 29/31 jobs, job order,
XOF/message length, stream IDs, service claims, every balancer counterpart,
and the forged-rho disconnect. Root-side one-worker release gates pass:
11/11 U5 library tests, the canonical-root proof, the ignored adversarial
matrix, and the ignored six-block/180-permutation service composition.
The full `stwo-mldsa` release suite reports 125 passed and 3 ignored; package
formatting, scoped warnings-denied Clippy, and `git diff --check` pass.
Independent final review found no P0–P3 issue and signed off the standalone
U5 patch. The actual composed U5→U6→U9 forged-`A_hat` gate remains mandatory
after those consumers exist.

### Phase-1 independent AIR/integration audit — 2026-07-29

The isolated private-message provider (7/7), private-MSO binder (10/10), and
full-padded-stream SHA tests (11/11) pass. Offset/slack decompositions prevent
M31 wraparound; complete UTC tdates and inclusive comparisons match the
removed host semantics; raw MSO plus SHA padding are mirrored exhaustively;
relation polarity is correct; product omits the MSO SHA; and same-shape binder
tree-zero material is credential-independent.

The composed Phase-1 proof has no sign-off yet. Verification simultaneously
requires a zero-projected issuer message and calls legacy host parsers on that
zero message. Its `mso_start` negative tuple has no scanner consumer; no
item-digest scanner sites exist; and old `PublicDigestBind` remains the
authoritative valueDigests path. Provider multiplicities currently include
only binder reads and must be rebuilt from checked-added binder+scanner
censuses. Whole-proof tree zero and serialization still contain credential
offsets, anchors, digest IDs, values, and dates, and cache v4 omits the
binder's docType-length shape determinant. That omission becomes a soundness
risk once the fail-closed host parser is removed: the binder's docType byte
enables are preprocessed, so a memoized shorter-docType root could omit issuer
relation bindings for a longer suffix. A-730's final cache-v5 cut must add the
canonical docType byte length and prove fresh/memoized root agreement plus key
separation across otherwise-identical lengths.

These are not candidates for completeness-only bypasses. Q-732/Q-734/Q-735
must select the scanner/version/normalization contracts, after which the
legacy host/public paths are deleted and the proof-level negative,
serialization, and cache matrix is run.

A second private-item review found no isolated arithmetic, relation-polarity,
offset-wrap, or fixed-claim defect (16/16 focused release tests pass), but
found one additional compatibility decision. Current product v1 decodes both
item layers with permissive Ciborium and no exact-consumption/canonical
re-encoding check; the private semantic parser requires minimal/definite
tokens, the exact tag-24/bstr prefix, and no trailing data. Q-738 asks whether
the single compatibility cut may reject those legacy encodings or must carry
a bounded exact-v1 parser. The same review confirms that Q-734/Q-735 and
proof-level parser/digest relation negatives remain mandatory before sign-off.

The follow-up dead-path sweep removed the superseded U0a
example/configuration and the unreachable issuer-field half of the U0b Keccak
probe. It also collapsed `MdocRevocationRangeBind` to its only constructed
mode: the private MSO SHA digest relation plus the private revocation-message
relation. The live geometry is unchanged at 336 trace columns and 48
interaction M31 columns. TS13 public verifier reconstruction now carries
neither a private range nor an invented zero revocation signature. Focused
release tests pin that public-only projection, the fixed relation geometry,
and rejection of a tampered provider-side revocation message.

The broad fully-PQ e2e currently proves and then stops at the already-known
Phase-1 boundary: its first legacy direct verify passes the prover-side
statement, and the public-auth projection guard correctly rejects the private
issuer/signature witnesses. This is not a cleanup regression or a candidate
for bypass. The e2e moves to the final public statement only after the pending
Q-732/Q-734/Q-735/Q-738 scanner/item rulings close all host-parser gaps.

The bounded U3 sweep removed the serialized age/nationality attribute-index
caches and their tree-zero material. Prover, verifier, TS13, and SDK now derive
the positions from the ordered public identifier/mode list; the release prover
library reports 59/59 and four exact SDK/integration controls report 1/1 each.
The stale test-only `Ts13MdocProofArtifact` was also deleted: it called the
generic verifier and bypassed the real TS13 profile/resource/proof-shape
checks. The SDK `Ts13ProofEnvelope` path is the sole authoritative gate.

That SDK gate now proves successfully and then returns `false` at the same
known boundary: public projection zeroes the issuer message, while
`check_mldsa_device_key_binding` and `mldsa_public_mso_facts` still parse it
before STARK verification. A relation-census audit also confirms the private
MSO binder emits one negative `MdocMsoStartRelation` tuple with no consumer,
and `mdoc_private_item_bind.rs` is not yet wired into the production claim
order. Q-732 owns that scanner/start consumer and its checked provider census;
Q-734/Q-735/Q-738 own the private version, predicate-normalization, and v1
CBOR-language choices needed before the item binder can replace the legacy
host/public paths.

The private issuer-message provider now has proof-level multiplicity evidence.
A minimal test-only `FieldBytes` consumer composes with the real provider
through `air_core::prove/verify`: the honest 37-byte control uses every index
once and verifies, while missing first/middle/last and extra-middle use proofs
reject at the exact global LogUp cancellation check. A separate exhaustive claim test
pins ±1 at every fixture position plus the largest non-wrapping M31
multiplicity and indexed overflow. The module reports 8/8 release tests.
This closes the isolated provider contract; the final Phase-1 proof must still
repeat the totality rail against the actual hosted issuer µ consumer after the
scanner census is added.

A real production-PCS proof of the private MSO binder first uncovered an
underreported constraint degree. Consecutive live LogUp sites enforce
`Δ·d1·d2 = n1·d2 + n2·d1`; two linear denominators make that identity cubic.
A follow-up degree census then found that the old issuer key multiplied the
private `window_offset` by a selector, making each issuer denominator
quadratic and a pair's recurrence quintic.

The lower-cost repair keeps the intended cubic budget rather than raising it
to `log N + 3`. The active payload-anchor row now sets and constrains
`window_offset=0`; inactive rows remain freshly blinded. AIR evaluation and
packed interaction generation share one linear issuer-index expression:
`payload_offset + chunk_relative + byte_index +
mso_window·payload_anchor_len + window_offset`. A symbolic polynomial-degree
regression rejects the old product form. Both `MdocPrivateMsoEval` and its
prover retain the exact `log N + 2` bound and polynomial coefficients without
adding a committed column.

The six-column test counter supplies the exact opposite issuer/SHA/start
relation signs. Its honest full-profile proof verifies under the production
PCS config, while shifted payload anchor/start, raw MSO byte, SHA padding
marker/zero/bit-length, and missing/extra start-use counterparts all reject at
the pre-STARK global LogUp check. A second honest proof verifies under the
default minimum-blowup PCS configuration, exercising coefficient-backed
domain extension. The binder module reports 13/13. The repair changes no
claim, relation order, layout, tree-zero material, transcript field, or
serialization; the planned global constraint-system cut already owns the
identity update.

A follow-up degree census found the same underreported paired-LogUp bound in
the private IssuerSignedItem binder. Its consecutive trace-linear
denominators make
`Δ·d1·d2 = n1·d2 + n2·d1` cubic, so both evaluator and prover now report
`log N + 2` and the prover retains polynomial coefficients. Claims, relation
order, committed columns, public mixing, tree-zero material, and serialization
are unchanged; A-730's single final constraint-system cut already owns the
identity change.

A compact five-family counter supplies the exact opposite `item_fields`,
outer/inner parsed-CBOR, `inner_raw`, and digest-ID relation tuples. Its honest
production-PCS composition verifies, while one representative tuple mutation
per family rejects specifically at the global LogUp cancellation check. Static
tests pin both degree declarations and coefficient retention. The focused
release item-binder module reports 17/17; formatting and `git diff --check`
pass.

The degree-seven private CBOR parser now requests polynomial coefficient
retention itself instead of relying on an unrelated co-composed SHA, MSO, or
item module. A minimal real composition uses the existing private-message
provider as the exact opposite raw-byte relation: all three parser rows
balance, and prove plus verify succeeds under `PcsConfig::default()` at minimum
blowup. The combined release prover library reports 65/65, the release SDK
library remains 29/29, and `unlink-spikes` examples check. Independent
degree/sign/layout reviews found no outstanding P0–P3 issue across the MSO,
item, and CBOR repairs.

### WO-U4 reduced public-exposure checkpoint — 2026-07-29

Commit: `5244904f`.

The TS13 exposure inventory now states the exact revocation anonymity
boundary: the public authority key and epoch are verifier inputs, and the
epoch deliberately partitions the anonymity set. The derived revocation id,
`id_lo`, `id_hi`, private MSO digest, and revocation signature are absent from
the clear public statement/transcript input surface. A-741 puts proof-wide
masking out of scope, so this checkpoint makes no endpoint-indistinguishability
or unlinkability claim.

A focused CBOR schema/round-trip regression proves the public TS13 statement
contains `revocation_public_key` and `epoch` but no `id`, `id_lo`, `id_hi`,
`signature`, or `mso_digest` field. The paired inventory regression pins the
public/private classifications. All three focused release inventory tests,
formatting, and `git diff --check` pass.

### Phase-1 implementation and acceptance checkpoint — 2026-07-29

The authorized U1/U2/U3/reduced-U4 landing is complete. The issuer ML-DSA
message, MSO payload, issuer/device/revocation signatures, revocation range,
private digest IDs, item values/randomizers, validity timestamps, and
credential-selected valueDigests entries are witness-only. Production now
composes the private message provider, strict outer/inner item CBOR parsers,
154-column private item binders, the celes-2.8.2 country table, the fixed
log-9 canonical multi-namespace valueDigests scanner, the private MSO binder,
the conditional namespaced MSO SHA, and the private revocation relation.
Provider use counts are checked-added from the final binder and scanner
censuses before the issuer provider is instantiated. Prover and verifier use
the same module and transcript order.

The compatibility cut is singular: product envelope V7, TS13 envelope V3,
constraint system v10, and tree-zero cache v5. The v10 tuple pins scanner
geometry `(log=9,max_items=255,preprocessed=4,trace=324,sites=51,
interaction=108)` plus the celes-2.8.2 table geometry and golden SHA-256.
Pre-V7/pre-V3 envelopes fail before body decode. Tree-zero material contains
only verifier-known shape/policy/cap determinants, including canonical
docType length. Fresh and memoized roots agree for genuinely different
same-public-shape credentials; changed policy and docType length separate
cache keys.

The final U3 wire regression builds two presentations of one high-digest-ID
credential under different nonces and one genuinely different credential
with the same public preprocessing determinants. After removing the exact
public nonce/device-auth challenge, all public statement bytes are equal.
Tree zero is equal across all three proofs. The exact Phase-1 stable-region
whitelist has two full-byte entries: the 1,952-byte device public key and the
issuer trust public key. Full MSO bytes, high digest-ID+digest contexts,
validity timestamps, `valid_today`, issuer Sig_structure/signature fragments,
device signature fragments, private item values, and item randomizers occur
neither in the wire envelope nor the decompressed proof. The ignored Phase-2
gate uses an empty device-key whitelist and rejects every common device-key
run of at least 32 bytes.

Release verification is green:

- `eu-id-prover` library: 99 passed; `unlink-spikes`: 101 passed.
- Full mdoc integration: 27 passed.
- `stwo-sha256`: 165 passed plus 18/18 ignored gates.
- `stwo-mldsa`: 110 passed plus 1/1 ignored gate.
- `stwo-keccak`: 34 passed; predicates: 66; Air Core: 18.
- SDK library: 33; product e2e: 7; TS13 e2e: 7; FFI: 2.
- Release workspace/all-target check, strict release all-target Clippy with
  warnings denied, formatting, and `git diff --check` pass.

Three fresh 12-core release processes give the following Phase-1 numbers:

| Gate | Run 1 | Run 2 | Run 3 | Median |
| --- | ---: | ---: | ---: | ---: |
| `phase1_prove_ms` (TS13 core) | 742 | 769 | 759 | 759 |
| `phase1_verify_ms` (forced-fresh) | 48 | 49 | 42 | 48 |
| `phase1_proof_bytes` (raw) | 1,552,867 | 1,557,427 | 1,555,443 | 1,555,443 |
| TS13 core Bzip2 wire bytes | 1,213,977 | 1,220,424 | 1,217,117 | 1,217,117 |
| Product SDK prove ms | 609 | 615 | 627 | 615 |
| Product SDK verify ms | 85 | 86 | 86 | 86 |
| `phase1_envelope_bytes` (product) | 1,248,787 | 1,247,593 | 1,238,851 | 1,247,593 |
| TS13 SDK prove ms | 851 | 887 | 847 | 851 |
| TS13 SDK first verify ms | 93 | 94 | 95 | 94 |
| TS13 SDK document wire bytes | 1,229,490 | 1,228,810 | 1,229,517 | 1,229,490 |

The realistic seven-attribute fixture has a 2,513-byte MSO, so
`phase1_revocation_sha_rows=2560` and 40 SHA blocks. The named timing is a
conservative whole-bridge upper bound:
`phase1_revocation_sha_ms<=198`, obtained from the Phase-1 core median minus
the U0a median. It includes scanner, binder, and normalization work; it is
deliberately not presented as an isolated SHA attribution. The isolated
normalization matrix reports `u3_normalization_prove_ms=52`, the median of 15
one-worker release composed proofs. The 769 ms maximum remains below the
work-order's 607×1.3 = 789 ms worst-case ceiling.

This checkpoint does **not** claim unlinkability or zero knowledge. After
Phase 1 the device public key is still a credential-stable public value, so
presentations of the same credential remain linkable by that key. The
published flag remains `zero_knowledge=false`. Per A-733, no U5/U6/U7/U9
Phase-2 implementation, export, feature, or file is active here. A-741
supersedes A-737 and removes Phase 3/ZK design, review, implementation, and
measurement from scope; `zero_knowledge=false` remains the final boundary.
