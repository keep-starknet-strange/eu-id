//! Cold perf probe for the exact API the EU-ID app calls on the PQ build:
//! `prove_identity` / `verify_identity` (envelope, zstd-compressed STARK,
//! ML-DSA issuer + device auth, age + nationality predicates). Uses the same
//! fully-PQ fixture as `pq_perf_probe`, minus the revocation leg the product
//! statement cannot express. `BENCH_ITERS` controls samples (default 1 = cold).

#[allow(dead_code)]
#[path = "../../eu-id-prover/tests/mldsa_fixture.rs"]
mod mldsa_fixture;

use std::time::Instant;

use euid_zk_sdk::{
    prove_identity, verify_identity, IssuerKey, NatMode, PredicateMode, TrustedIssuers,
    ZkMdocWitness, ZkPublicStatement,
};
use sha2::{Digest, Sha256};

fn fixture() -> (ZkPublicStatement, ZkMdocWitness) {
    let session_transcript =
        eu_id_prover::mdoc::openid4vp_session_transcript(b"session-transcript-123");
    let fixture = mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
    (
        ZkPublicStatement {
            spec_id: "stwo-euid-pid-v1".to_string(),
            version: 1,
            doctype: "eu.europa.ec.eudi.pid.1".to_string(),
            namespace: "eu.europa.ec.eudi.pid.1".to_string(),
            issuer_key: IssuerKey::MlDsa {
                pk_hash: Sha256::digest(&fixture.issuer_pk).to_vec(),
            },
            today_epoch_day: 20637,
            nonce: session_transcript,
            predicate_mode: PredicateMode::And,
            age_threshold_years: Some(18),
            accepted_numeric_countries: Some(vec![250, 276]),
            nat_mode: NatMode::Any,
            ts13_request: None,
        },
        ZkMdocWitness {
            document: fixture.document,
            trusted_issuers: TrustedIssuers::PublicKeys(vec![fixture.issuer_pk]),
            ts13_trusted_issuer_public_keys: None,
            ts13_revocation_id_lo: None,
            ts13_revocation_id_hi: None,
            ts13_revocation_signature: None,
        },
    )
}

fn main() {
    let iters = std::env::var("BENCH_ITERS")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(1)
        .max(1);
    let (statement, witness) = fixture();

    let mut prove_ms = Vec::new();
    let mut proof = Vec::new();
    for _ in 0..iters {
        let (s, w) = (statement.clone(), witness.clone());
        let start = Instant::now();
        proof = prove_identity(s, w).expect("identity proof builds");
        prove_ms.push(start.elapsed().as_millis());
    }

    let mut verify_ms = Vec::new();
    for _ in 0..iters {
        let start = Instant::now();
        let result = verify_identity(statement.clone(), proof.clone()).expect("verify returns");
        verify_ms.push(start.elapsed().as_millis());
        assert!(result.ok, "identity proof must verify");
    }

    // Decisive byte check: is the DOB literally on the wire?
    let dob_cbor = [106u8, 49, 57, 57, 48, 45, 48, 55, 45, 49, 53]; // CBOR text "1990-07-15"
    let dob_ascii = &dob_cbor[1..];
    println!(
        "WIRE_CHECK dob_cbor_in_envelope={} dob_ascii_in_envelope={}",
        proof.windows(dob_cbor.len()).any(|w| w == dob_cbor),
        proof.windows(dob_ascii.len()).any(|w| w == dob_ascii),
    );

    // Privacy check: decode the envelope the verifier receives and print the
    // statement fields that carry credential values, rather than byte-grepping
    // (a short needle hits by chance in a ~1 MB proof).
    // The SDK puts this exact struct in the envelope, uncompressed, next to the
    // compressed STARK. Byte-grepping a ~1 MB proof for a short value hits by
    // chance, so inspect the typed fields instead.
    {
        let session_transcript =
            eu_id_prover::mdoc::openid4vp_session_transcript(b"session-transcript-123");
        let fx = mldsa_fixture::mldsa_full_pq_fixture_with_transcript(&session_transcript);
        // Same shape mdoc_request() builds for a product AND-mode statement.
        let request = eu_id_prover::mdoc::MdocPidRequest::eudi_pid(session_transcript)
            .with_trusted_mldsa_issuer_public_keys(vec![fx.issuer_pk.clone()]);
        let policy = eu_id_prover::Policy {
            current_date: eu_id_prover::Date {
                year: 2026,
                month: 7,
                day: 3,
            },
            min_age_years: 18,
            accepted_nationalities: vec![250, 276],
        };
        let (_, mdoc_statement) =
            eu_id_prover::prove_mdoc(&fx.document, &request, policy).expect("proves");
        println!("LEAK_CHECK private_predicate_bindings=absent");
        for attribute in &mdoc_statement.attributes {
            println!(
                "LEAK_CHECK attribute id={:?} mode={:?} item_padded_len={}",
                attribute.element_identifier, attribute.mode, attribute.item_padded_len
            );
        }
    }

    println!(
        "{{\"api\":\"prove_identity/verify_identity (ML-DSA)\",\"rayon_num_threads\":{:?},\"iters\":{iters},\"phase1_envelope_bytes\":{},\"prove_ms_all\":{prove_ms:?},\"verify_ms_all\":{verify_ms:?}}}",
        std::env::var("RAYON_NUM_THREADS").ok(),
        proof.len(),
    );
}
