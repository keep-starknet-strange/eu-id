# Campaign lessons

- Before calling a benchmark a full identity or revocation proof, trace its exact FFI entrypoint,
  fixture constructor, and optional statement fields. Keep legacy `identity`, default mdoc, and
  revocation-enabled mdoc labels separate; do not infer revocation from a benchmark name.
- Performance reports must set and record `RAYON_NUM_THREADS` explicitly. A default Rayon run is
  multithreaded even when the product's `parallel` feature is not named directly, because dependency
  feature unification can enable Stwo's parallel paths. Every benchmark result line must expose the
  effective Rayon thread count before it is compared with a one-thread campaign baseline.
- The full-PQ end-to-end acceptance gates are hard: issuer, device, and revocation must all use
  ML-DSA-65; `pq_perf_probe` must run in release mode with `RAYON_NUM_THREADS=1` and the production
  PCS config; prove must be under 1,000 ms, verify must remain under 100 ms, and the proof must remain
  under 1,000,000 bytes. A campaign may document a blocked approach, but it must not reclassify an
  unmet hard gate as unreachable or complete.
- "Full-PQ proven in a STARK" fixes the trust boundary: issuer, device, and revocation ML-DSA-65
  verification must all remain inside the STARK, and the existing production PCS parameters are
  immutable unless the user explicitly authorizes a protocol change. Native verification or merely
  renaming a faster PCS point is not a valid performance optimization and its measurements must be
  retracted immediately.
- A STARK verifier that accepts the prover's preprocessed-tree commitment without an independently
  supplied root does not have trusted constants or lookup tables. Product verification must fail
  closed unless tree 0 is pinned by the verifier; a root copied from the proof or its envelope is not
  a pin.
- Transcript-mixing a derived public value proves agreement with that value, not its derivation.
  For exact ML-DSA, `tr` must be constrained to `SHAKE256(pkEncode(rho, t1), 64)` (or be derived by
  an explicitly accepted public-input canonicalization boundary); treating a caller-supplied `tr`
  as free weakens the FIPS relation.
- Honest-vector and witness-mutation tests cannot establish AIR soundness. Audit every state column,
  transition, permutation tuple field, and relation multiplicity directly; zeroed lookup gates and a
  field omitted from a memory tuple can leave honest proving green while admitting adversarial traces.
- When the requirement is literally "everything proven in a STARK," a transcript-bound GKR payload
  verified by native code is still out of scope. Remove native acceptance hooks, make the outer AIR
  constrain the result, and separately disclose any verifier-derived public preprocessing (such as
  `ExpandA(rho)`) that has not itself been traced; do not call the result fully all-arithmetic-in-AIR.
- Distinguish AIR self-containment from end-to-end soundness: deterministic public preprocessing
  recomputed by the verifier can be a valid application trust boundary even when that derivation is
  not traced. State that boundary precisely and let the integration requirement decide whether it
  is acceptable; do not describe the whole flow as unusable merely because it is not self-contained.
- When closing a public-derivation boundary, a post-proof claim mutation is not enough as the main
  regression. Also give the prover a self-consistent forged derived witness and prove that the AIR
  rejects its missing link to the canonical source transcript.
- For heterogeneous mobile CPUs, thread count is not a sufficient benchmark policy. Pin the prover
  pool to explicitly selected performance-core CPU IDs, exclude the lowest-capacity cluster, and
  record selected/excluded IDs plus the topology source; use an unpinned all-core run only when the
  user explicitly asks for it.
- A late prover optimization is not covered by an earlier candidate's phone results. Give the final
  shipped source its own same-APK, counter-ordered physical-phone A/B gate and keep it only when every
  target clears a predeclared usefulness threshold without verifier, proof-size, memory, affinity,
  provenance, or full-proof-success regression.
- A cross-domain lookup negative must isolate the domain tag: move matching consumer and provider
  multiplicities so the forged multiset would balance if tags were erased, then require rejection
  with tags retained. Mutating only the consumer proves generic lookup imbalance, not tag separation.
- Test attack state read by AIR evaluation cannot remain thread-local when quotient evaluation may
  run on Rayon workers. Snapshot it once into immutable relation/eval state so shape inference,
  interaction generation, prover workers, and verifier reconstruction all exercise the same attack.
- A malformed optional-arm regression must first build a fixture that actually contains that arm.
  Prove the three-role control fixture before shortening or extending revocation claim vectors.
- Before reporting a repository-required file as absent, search hidden tracked
  paths too (`rg --files -uu` or `git ls-tree -r HEAD`); ordinary file
  discovery can omit `.agents` and turn a search mistake into a false
  protocol-escalation premise.
- An exact Cargo test filter is not evidence unless the result reports at
  least one executed test. Confirm the fully qualified module path and the
  nonzero `passed` count; a green `0 passed` run is only a filter typo.
- Hold every verifier-preprocessing determinant fixed in cross-credential
  privacy-region comparisons, especially the public device key. Otherwise a
  legitimate tree-zero change is indistinguishable from a private-witness
  leak; test the known public key exposure in a separate exact-whitelist gate.
- Run every Cargo gate for this proof system with release optimizations.
  Repeating debug proofs adds wall-clock cost without improving protocol
  diagnosis. If symbols are needed, add a release-optimized profile that keeps
  debug information instead of falling back to the dev profile.
