# A-015 layered candidate acceptance

Decision authority: Fable, 2026-08-02

Final disposition: sound; rejected on measured phone throughput, 2026-08-02

This file preserves the A-015 soundness decision. c7 is not the canonical
proof path.

The package provenance in Q-015 is accepted and recorded.

The committed-bit v3 document was suspended. The committed-nibble design in
`docs/ts13-keccak-layered-gkr.md`, at soundness-source commit `2111a1eb`, was
the reviewed acceptance candidate. It uses 400 committed spread-nibble input
columns.
The bit layer is internal and deterministic. Both tie-backs anchor the layer
chain to committed columns. This design uses less commitment mass than the
committed-bit repair.

The independent review at evidence-ledger commit `358646b1` accepts the
protocol as sound. It reports no critical or high finding. The review checks
these items:

1. The constraints force every committed input cell into the exact 16-value
   spread-nibble domain.
2. The extraction polynomials are correct and stay within the engine degree
   limit.
3. All 72 layers have correct wiring, active-permutation masks, dead-lane
   masks, and Iota gates.
4. Both boundary flows and MLE tie-backs bind the correct claims, points, and
   transcript order. Every challenge follows the required transcript mixes.
5. The old carrier, round GKR, and schedule table are fully retired. The new
   interaction graph has global balance and no disconnected multiset.
6. The payload wire has complete gates and bounded decoding.
7. One whole-system soundness calculation includes the retained STARK, OODS,
   FRI, and proof-of-work terms. It uses the same accounting as the live
   baseline. It omits no new term class and keeps every other term unchanged.
8. Both the replacement and complete-Keccak census reconcile to the source.

A-015-review names circuit hash
`3fac167754de85508fd6fda45e37043f6e104821463b9fa40e17d88fa4938b9c`.
A-016 withdraws the stale literal 108-bit gate. The candidate must preserve or
improve the live whole-system algebraic bound under identical accounting. The
recorded live baseline is about 105.91 bits before global LogUp collision
terms.

The review requires three conditions before final campaign acceptance:

1. State the actual artifact binding for the Keccak constants and payload.
2. Add one exported `verifyIdentity` negative for a recomposition-neutral,
   off-domain input-nibble pair.
3. State that the removed carrier baseline is not independently recomputable.

Land these conditions before artifact generation. Then generate a new circuit
hash and rerun the full release matrix. Use only that final hash for the
three-phone acceptance run.

The desktop result was 1,784 ms for proving, 80 ms for verification, and
777,682,944 bytes of peak resident memory. Proving was slower than the
pre-layered 1,162 ms path. The final c7 matrix measured 13,560 ms on Pixel 8,
5,075 ms on Galaxy S24 Ultra, and 9,523 ms on Galaxy A54. All three phones
failed the 2,000 ms gate. A-018 restored P5 as the canonical path.

A-018-route authorizes an authenticated witness-MLE opening primitive in `~/stwo` on a
dedicated branch from `dev-copy`. P5 must stay canonical while that work
continues. The application STWO pin does not move without a recorded repin
decision, proof-byte parity evidence, and a demo-baseline guard.

A-016 retires the earlier A54 complete-Keccak limit of 1,200 ms because the
current timing wire cannot measure it. The binding performance gate is one
cold `proveIdentity` call below 2,000 ms on each of the three phones. The
desktop 25-phase record must stay with the phone evidence.
