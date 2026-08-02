# A-020 performance campaign closure

Decision authority: Lucas, 2026-08-02

Final disposition: the TS13 phone proving campaign is closed at the verified
P5 baseline. The 2,000 ms three-phone proving target is formally retired.

P5 remains canonical. The c7 design remains sound but rejected on measured
phone throughput. A-019 closes the authenticated-MLE engine route. A future
proof-system project needs a new decision.

The canonical source restore is `1e035312`. Its artifact commit is
`cdfdf52c`, and its circuit hash is
`6b30e79449d331477027412fd30c831f7bb45cea42214b072845173fea0241b6`.
The privacy claim remains `public-input unlinkable; transcript zero knowledge
pending`.

The canonical campaign state and the section 11.7-conformant resource record
are in `docs/p6-campaign-decisions.md`. This file is the tracked decision
mirror for main-repository mailbox `A-020-campaign-closed-at-p5.md`. It does
not define another protocol, artifact, benchmark, or API path.
