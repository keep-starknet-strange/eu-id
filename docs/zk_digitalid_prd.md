PRD: STARK-based Zero-Knowledge Proofs for the EU Digital Identity Wallet
Background
The EU is building a Digital Identity Wallet that every Member State must offer to citizens by end of 2026. A core promise of the wallet is privacy — citizens should be able to prove things about themselves (over 18, resident in country X, holds a valid driving licence) without revealing more than necessary, and without being trackable across uses.
The cryptographic technique that makes this possible is called a Zero-Knowledge Proof (ZKP). The European Commission is currently deciding which ZKP technologies to recommend for the wallet. That decision is being made in public, in a working document called “Topic G” and on a GitHub discussion thread where Member States, telecom operators, data protection authorities, and cryptography researchers contribute.
The problem
The Topic G working document considers two families of ZKP technology: BBS+ signatures and zk-SNARKs. A third major family — STARKs — is missing from the analysis entirely. The omission has been noted briefly in the discussion thread but no one has put forward a concrete technical case for including STARKs in the recommendation.
This matters because STARKs have properties the other two families don’t:
Post-quantum security by default — they’re not broken by future quantum computers. The other families need to be redesigned to survive PQ migration.
No trusted setup — zk-SNARKs typically require a one-time ceremony where if the participants cheat, the entire system is broken. STARKs don’t.
Proven scalability — STARKs are what powers Starknet and several Bitcoin/Ethereum scaling systems today, with billions of euros of transaction volume.
What this project does
We build a working proof-of-concept demonstrating that STARKs can do the same job as zk-SNARKs in the EU wallet context, on the same kind of credential, with measurable performance numbers on real hardware. We then submit that POC to the public discussion as a concrete contribution.
The specific demonstration: proving “I am over 18” from a digitally signed identity credential, without revealing my date of birth or any other information about me. This is the most-cited use case in the wallet documentation and the easiest for non-technical readers to grasp.
Why now
Three reasons:
The decision window is open. The Topic G document is a working draft, actively being amended based on community feedback. A well-grounded contribution now can change what gets standardized. After the document is finalized, changing the recommendations becomes much harder.
STARK tooling has matured. Independent benchmarks (FibRace, October 2025) showed STARK proofs being generated on consumer smartphones in under 5 seconds across 1,400 different device models in 99 countries. Two years ago this POC wouldn’t have been possible; today the foundation is solid.
Post-quantum migration is on the European agenda. ETSI is working on PQ profiles, NIST has standardized the first PQ signature schemes, and the wallet will need to migrate eventually. A privacy technology that’s PQ-ready by design is more valuable as that migration approaches.
What we’re building
A software project published as open source on GitHub, containing:
A working implementation of “prove age-over-18 from a digitally signed credential” using the Stwo STARK framework
Benchmark results showing proof generation time, proof size, memory usage, and verification time, on both laptop and (target) mobile hardware
A short technical writeup comparing our results to the zk-SNARK alternatives the Topic G document already considers
A formal comment posted to the official EU GitHub discussion, linking to the POC and proposing specific text additions to the Topic G document
The POC is deliberately scoped narrowly. We’re not building a wallet. We’re not building a production-ready library. We’re building the smallest credible technical artifact that demonstrates STARKs belong in the conversation.
What success looks like
Minimum success: the POC works end-to-end, produces honest performance numbers, and is posted to the discussion thread with proposed text additions to Topic G. Whether or not the EU adopts the recommendation, we’ve added a missing technical perspective to a public-record decision.
Strong success: the Topic G document is amended in a future revision to include STARK-family schemes in its taxonomy, with our POC cited as the supporting evidence.
Stretch success: one or more of the Member State implementations or Large Scale Pilot projects picks up STARK-based selective disclosure as a candidate technology to evaluate for their own wallet.
What we’re explicitly not doing
Not building a production-grade prover. The POC is a research prototype.
Not advocating that STARKs replace BBS+ or zk-SNARKs. The honest claim is “STARKs should be in the candidate set the EU is comparing.” Different schemes will win for different use cases.
Not solving every cryptographic property the Topic G document discusses. Properties like privacy-preserving revocation and full unlinkability against issuer-verifier collusion are out of scope for the first iteration.
Not implementing zero-knowledge masking in the first iteration. The POC will produce succinct proofs (small, fast to verify) but not yet zero-knowledge proofs (which additionally hide all information about the witness). This is clearly disclosed in the writeup, and the masking technique to add ZK is well-understood in the literature.
Risks
Performance risk. Proof generation may be too slow or use too much memory for mobile devices in the first iteration. Mitigation: we benchmark early (after week 2) on the simplest component before sinking effort into the full system. If the cryptographic primitives don’t fit, we narrow scope rather than ship a misleading result.
Technical risk. Building cryptographic gadgets correctly is hard, and silent bugs can break the security guarantees without breaking the tests. Mitigation: extensive property-based testing against a reference implementation at every layer. We don’t claim audit-quality security — the writeup says explicitly this is a research prototype.
Reception risk. The EU working group may dismiss the contribution for non-technical reasons (timing, organizational politics, preference for established schemes). Mitigation: we frame the contribution as additive, not adversarial. We’re filling a gap in their analysis, not contesting their recommendations.
Timeline
Roughly 6–8 weeks of focused engineering work, broken into:
Weeks 1–2: Set up the framework, get a baseline benchmark, build the simplest cryptographic gadgets.
Weeks 3–4: Build the elliptic-curve and signature-verification components — the technically hardest part.
Weeks 5–6: Add the credential parsing and the age-over-18 logic. Wire everything together.
Weeks 7–8: Benchmark, write up, post to the EU discussion.


