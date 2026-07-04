use std::path::{Path, PathBuf};

use crate::ecdsa::implemented_circuit_gate_count;
use crate::ligero::{v1_ligero_params, V1_MIN_OPENINGS, V1_NON_ZK};

const G1_FIELD_BENCH: &str = "WO-G1-field-bench.md";
const G2_SUMCHECK_BENCH: &str = "WO-G2-sumcheck-bench.md";
const G4_CIRCUIT_INVENTORY: &str = "WO-G4-circuit-inventory.md";

const G1_MAX_INDEPENDENT_NS_PER_MULT: f64 = 25.0;
const G2_MAX_MS_PER_35K_QUAD_EQUIV: f64 = 20.0;
const G4_MAILBOX_GATE_COUNT: usize = 33_000;

#[test]
fn g1_field_bench_result_is_recorded_and_meets_gate() {
    let result = result_block(&task_file(G1_FIELD_BENCH));
    let independent_ns = parse_number(&result, "independent_ns_per_mult");

    assert!(
        independent_ns <= G1_MAX_INDEPENDENT_NS_PER_MULT,
        "G1 independent field multiplication is {independent_ns} ns/mult; gate is <= {G1_MAX_INDEPENDENT_NS_PER_MULT}"
    );
}

#[test]
fn g2_sumcheck_bench_result_is_recorded_and_meets_gate() {
    let result = result_block(&task_file(G2_SUMCHECK_BENCH));
    let ms = parse_number(&result, "ms_per_35k_quad_equiv");

    assert!(
        ms <= G2_MAX_MS_PER_35K_QUAD_EQUIV,
        "G2 sumcheck is {ms} ms/35k-quad-equiv; gate is <= {G2_MAX_MS_PER_35K_QUAD_EQUIV}"
    );
}

#[test]
fn q027_pinned_ligero_params_meet_v1_non_zk_soundness_gate() {
    let params = v1_ligero_params();

    assert_eq!(params.row_len, 64);
    assert_eq!(params.degree_bound, 64);
    assert_eq!(params.codeword_len, 512);
    assert_eq!(params.openings, 160);
    assert_eq!(params.proximity_radius, 223);
    assert!(V1_NON_ZK, "Q-027 tuple is valid only for the v1 non-ZK commitment");
    assert!(params.degree_bound >= params.row_len);
    assert!(params.openings >= V1_MIN_OPENINGS);
    params.validate().unwrap();
    assert!(
        params.soundness_error() <= 2f64.powi(-128),
        "Q-027 soundness error {} exceeds 2^-128",
        params.soundness_error()
    );
}

#[test]
fn g4_gate_count_is_recorded_and_below_mailbox_gate() {
    let result = result_block(&task_file(G4_CIRCUIT_INVENTORY));
    let recorded = parse_usize(&result, "measured_quad_count");
    let measured = implemented_circuit_gate_count().expect("static ECDSA circuits build");

    assert_eq!(
        recorded, measured,
        "G4 RESULT measured_quad_count must match the current builder"
    );
    assert!(
        measured <= G4_MAILBOX_GATE_COUNT,
        "G4 measured quad count {measured} exceeds mailbox threshold {G4_MAILBOX_GATE_COUNT}"
    );
}

fn task_file(name: &str) -> PathBuf {
    if let Ok(root) = std::env::var("S4_TASKS_DIR") {
        return PathBuf::from(root).join(name);
    }

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for ancestor in manifest_dir.ancestors() {
        let candidate = ancestor.join("tasks/parity/s4").join(name);
        if candidate.exists() {
            return candidate;
        }
    }

    PathBuf::from("/Users/lucas/eu-id/tasks/parity/s4").join(name)
}

fn result_block(path: &Path) -> String {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let Some(start) = text.find("## RESULT") else {
        panic!("{} is missing a ## RESULT block", path.display());
    };
    let rest = &text[start..];
    let end = rest
        .find("\n## ")
        .map(|offset| offset + start)
        .unwrap_or(text.len());
    text[start..end].to_owned()
}

fn parse_number(block: &str, key: &str) -> f64 {
    let raw = value_for_key(block, key);
    raw.parse::<f64>()
        .unwrap_or_else(|err| panic!("RESULT key {key} has non-numeric value {raw:?}: {err}"))
}

fn parse_usize(block: &str, key: &str) -> usize {
    let raw = value_for_key(block, key);
    raw.parse::<usize>()
        .unwrap_or_else(|err| panic!("RESULT key {key} has non-integer value {raw:?}: {err}"))
}

fn value_for_key<'a>(block: &'a str, key: &str) -> &'a str {
    let prefix = format!("{key}:");
    block
        .lines()
        .find_map(|line| {
            let line = line.trim().trim_start_matches('-').trim();
            line.strip_prefix(&prefix)
                .map(|value| value.trim().split_whitespace().next().unwrap_or(""))
        })
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| panic!("RESULT block is missing key {key}"))
}
