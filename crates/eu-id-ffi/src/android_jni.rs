use jni::objects::JClass;
use jni::sys::{jint, jstring};
use jni::JNIEnv;
use std::panic::{catch_unwind, AssertUnwindSafe};

use crate::{
    eu_id_bench_identity, eu_id_bench_mdoc, eu_id_bench_p256, eu_id_bench_sha256,
    EuIdIdentityBench, EuIdIdentityInput,
};

const SHA256_FIXTURE: &[u8] = b"eu-id mobile sha256 bench fixture";
const FAILED_JSON: &str =
    r#"{"prove_ms":0,"verify_ms":0,"peak_bytes":0,"proof_bytes":0,"ok":false}"#;

fn result_json(
    prove_ms: u64,
    verify_ms: u64,
    peak_bytes: u64,
    proof_bytes: u64,
    ok: bool,
) -> String {
    format!(
        r#"{{"prove_ms":{prove_ms},"verify_ms":{verify_ms},"peak_bytes":{peak_bytes},"proof_bytes":{proof_bytes},"ok":{ok}}}"#
    )
}

fn identity_json(result: EuIdIdentityBench) -> String {
    result_json(
        result.prove_ms,
        result.verify_ms,
        result.peak_bytes,
        result.proof_bytes,
        result.ok == 1,
    )
}

fn run_sha256(iters: u32) -> String {
    // SAFETY: the fixture is alive for the call and supplies its exact length.
    let result =
        unsafe { eu_id_bench_sha256(SHA256_FIXTURE.as_ptr(), SHA256_FIXTURE.len(), iters) };
    result_json(
        result.prove_ms,
        result.verify_ms,
        result.peak_bytes,
        0,
        result.ok == 1,
    )
}

fn run_p256(iters: u32) -> String {
    let input = eu_id_prover::fixtures::demo_nonce_statement().ecdsa_input();
    // SAFETY: all five fixed-width arrays are owned by `input` for the call.
    let result = unsafe {
        eu_id_bench_p256(
            input.message_hash.0.as_ptr(),
            input.signature.r.0.as_ptr(),
            input.signature.s.0.as_ptr(),
            input.public_key.x.0.as_ptr(),
            input.public_key.y.0.as_ptr(),
            iters,
        )
    };
    result_json(
        result.prove_ms,
        result.verify_ms,
        result.peak_bytes,
        0,
        result.ok == 1 && result.verified == 1,
    )
}

fn run_identity(iters: u32) -> String {
    let fixture = eu_id_prover::fixtures::valid_over_18();
    let credential = fixture.signed.credential;
    let policy = fixture.policy;
    let input = EuIdIdentityInput {
        birth_year: credential.birth_year,
        birth_month: credential.birth_month,
        birth_day: credential.birth_day,
        nationality: credential.nationality,
        current_year: policy.current_date.year as u16,
        current_month: policy.current_date.month as u8,
        current_day: policy.current_date.day as u8,
        min_age_years: policy.min_age_years,
        accepted: policy.accepted_nationalities.as_ptr(),
        accepted_len: policy.accepted_nationalities.len(),
    };
    // SAFETY: `input` and its policy-owned nationality buffer live for the call.
    identity_json(unsafe { eu_id_bench_identity(&input, iters) })
}

fn run_mdoc(iters: u32) -> String {
    // SAFETY: this entry point takes no pointers and catches prover panics.
    identity_json(unsafe { eu_id_bench_mdoc(iters) })
}

fn iteration_count(iters: jint) -> u32 {
    iters.max(1) as u32
}

fn into_jstring(env: &JNIEnv<'_>, value: String) -> jstring {
    env.new_string(value)
        .map(|value| value.into_raw())
        .unwrap_or(std::ptr::null_mut())
}

fn catch_json(work: impl FnOnce() -> String) -> String {
    catch_unwind(AssertUnwindSafe(work)).unwrap_or_else(|_| FAILED_JSON.to_owned())
}

#[no_mangle]
pub extern "system" fn Java_eu_euid_bench_BenchRunner_sha256(
    env: JNIEnv<'_>,
    _class: JClass<'_>,
    iters: jint,
) -> jstring {
    into_jstring(&env, catch_json(|| run_sha256(iteration_count(iters))))
}

#[no_mangle]
pub extern "system" fn Java_eu_euid_bench_BenchRunner_p256(
    env: JNIEnv<'_>,
    _class: JClass<'_>,
    iters: jint,
) -> jstring {
    into_jstring(&env, catch_json(|| run_p256(iteration_count(iters))))
}

#[no_mangle]
pub extern "system" fn Java_eu_euid_bench_BenchRunner_identity(
    env: JNIEnv<'_>,
    _class: JClass<'_>,
    iters: jint,
) -> jstring {
    into_jstring(&env, catch_json(|| run_identity(iteration_count(iters))))
}

#[no_mangle]
pub extern "system" fn Java_eu_euid_bench_BenchRunner_mdoc(
    env: JNIEnv<'_>,
    _class: JClass<'_>,
    iters: jint,
) -> jstring {
    into_jstring(&env, catch_json(|| run_mdoc(iteration_count(iters))))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn result_json_has_the_exact_wire_schema() {
        assert_eq!(
            result_json(1, 2, 3, 4, true),
            r#"{"prove_ms":1,"verify_ms":2,"peak_bytes":3,"proof_bytes":4,"ok":true}"#
        );
    }

    #[test]
    fn non_positive_iteration_counts_are_clamped() {
        assert_eq!(iteration_count(-1), 1);
        assert_eq!(iteration_count(0), 1);
        assert_eq!(iteration_count(5), 5);
    }

    #[test]
    fn wrapper_panics_become_failed_json() {
        assert_eq!(catch_json(|| panic!("fixture failed")), FAILED_JSON);
    }

    #[test]
    fn p256_fixture_populates_every_field() {
        let input = eu_id_prover::fixtures::demo_nonce_statement().ecdsa_input();
        assert_ne!(input.message_hash.0, [0; 32]);
        assert_ne!(input.signature.r.0, [0; 32]);
        assert_ne!(input.signature.s.0, [0; 32]);
        assert_ne!(input.public_key.x.0, [0; 32]);
        assert_ne!(input.public_key.y.0, [0; 32]);
    }
}
