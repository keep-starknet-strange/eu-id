use jni::objects::JClass;
use jni::sys::{jboolean, jstring};
use jni::JNIEnv;
use std::panic::{catch_unwind, AssertUnwindSafe};

use crate::{eu_id_bench_full_pq, EuIdFullPqBench};

const FAILED_JSON: &str = r#"{"prove_ms":0,"process_cpu_ms":0,"cold_verify_ms":0,"cold_tree0_root_ms":0,"cold_stark_verify_ms":0,"warm_verify_ms":0,"warm_tree0_root_ms":0,"warm_stark_verify_ms":0,"peak_bytes":0,"proof_bytes":0,"rayon_threads":0,"worker_cpu_ids":[],"excluded_cpu_ids":[],"core_metric":"unknown","ok":false}"#;

fn cpu_ids_json(mask: u64) -> String {
    let ids = (0..u64::BITS)
        .filter(|cpu_id| mask & (1_u64 << cpu_id) != 0)
        .map(|cpu_id| cpu_id.to_string())
        .collect::<Vec<_>>();
    format!("[{}]", ids.join(","))
}

fn core_metric_name(metric: u32) -> &'static str {
    match metric {
        0 => "host_available_parallelism",
        1 => "cpu_capacity",
        2 => "cpuinfo_max_freq",
        _ => "unknown",
    }
}

fn result_json(result: EuIdFullPqBench) -> String {
    let EuIdFullPqBench {
        prove_ms,
        process_cpu_ms,
        cold_verify_ms,
        cold_tree0_root_ms,
        cold_stark_verify_ms,
        warm_verify_ms,
        warm_tree0_root_ms,
        warm_stark_verify_ms,
        peak_bytes,
        proof_bytes,
        rayon_threads,
        worker_cpu_mask,
        excluded_cpu_mask,
        core_metric,
        ok,
    } = result;
    let ok = ok == 1;
    let worker_cpu_ids = cpu_ids_json(worker_cpu_mask);
    let excluded_cpu_ids = cpu_ids_json(excluded_cpu_mask);
    let core_metric = core_metric_name(core_metric);
    format!(
        r#"{{"prove_ms":{prove_ms},"process_cpu_ms":{process_cpu_ms},"cold_verify_ms":{cold_verify_ms},"cold_tree0_root_ms":{cold_tree0_root_ms},"cold_stark_verify_ms":{cold_stark_verify_ms},"warm_verify_ms":{warm_verify_ms},"warm_tree0_root_ms":{warm_tree0_root_ms},"warm_stark_verify_ms":{warm_stark_verify_ms},"peak_bytes":{peak_bytes},"proof_bytes":{proof_bytes},"rayon_threads":{rayon_threads},"worker_cpu_ids":{worker_cpu_ids},"excluded_cpu_ids":{excluded_cpu_ids},"core_metric":"{core_metric}","ok":{ok}}}"#
    )
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
#[allow(non_snake_case)]
pub extern "system" fn Java_eu_euid_bench_BenchRunner_fullPq(
    env: JNIEnv<'_>,
    _class: JClass<'_>,
    all_performance_cores: jboolean,
) -> jstring {
    into_jstring(
        &env,
        catch_json(|| result_json(eu_id_bench_full_pq(all_performance_cores != 0))),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn result_json_has_the_exact_wire_schema() {
        let result = EuIdFullPqBench {
            prove_ms: 1,
            process_cpu_ms: 2,
            cold_verify_ms: 3,
            cold_tree0_root_ms: 4,
            cold_stark_verify_ms: 5,
            warm_verify_ms: 6,
            warm_tree0_root_ms: 7,
            warm_stark_verify_ms: 8,
            peak_bytes: 9,
            proof_bytes: 10,
            rayon_threads: 3,
            worker_cpu_mask: 0b1_1100,
            excluded_cpu_mask: 0b11,
            core_metric: 1,
            ok: 1,
        };
        assert_eq!(
            result_json(result),
            r#"{"prove_ms":1,"process_cpu_ms":2,"cold_verify_ms":3,"cold_tree0_root_ms":4,"cold_stark_verify_ms":5,"warm_verify_ms":6,"warm_tree0_root_ms":7,"warm_stark_verify_ms":8,"peak_bytes":9,"proof_bytes":10,"rayon_threads":3,"worker_cpu_ids":[2,3,4],"excluded_cpu_ids":[0,1],"core_metric":"cpu_capacity","ok":true}"#
        );
    }

    #[test]
    fn wrapper_panics_become_failed_json() {
        assert_eq!(catch_json(|| panic!("fixture failed")), FAILED_JSON);
    }
}
