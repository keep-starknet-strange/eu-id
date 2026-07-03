//! FRI config sweep for WO-3.3.
//!
//! Run with:
//! `cargo run -p eu-id-prover --example fri_sweep --features fri-sweep`

use std::env;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Instant;

use eu_id_prover::{fixtures, prove_with_column_breakdown_and_config, verify_with_config};
use stwo::core::fri::FriConfig;
use stwo::core::pcs::PcsConfig;
use stwo::tracing::SpanAccumulator;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::Registry;

const CURRENT_POW_BITS: u32 = 10;
const CURRENT_LOG_BLOWUP: u32 = 2;
const CURRENT_LAST_LAYER: u32 = 5;
const CURRENT_FOLD_STEP: u32 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Case {
    pow_bits: u32,
    log_blowup: u32,
    log_last_layer: u32,
    n_queries: usize,
    fold_step: u32,
}

#[derive(Clone, Debug)]
struct Row {
    case: Case,
    prove_ms: f64,
    verify_ms: f64,
    proof_bytes: usize,
    composition_ms: f64,
    verified: bool,
}

fn main() {
    let samples = env::var("FRI_SWEEP_SAMPLES")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(1);

    let fixture = fixtures::valid_over_18();
    let witness = fixture.pipeline_witness();
    assert!(
        witness.check_consistency().all_ok(),
        "valid_over_18 fixture must be internally consistent"
    );
    let draft = witness
        .p256_draft
        .as_ref()
        .expect("valid_over_18 has a valid P256 draft");

    let fold_steps = supported_fold_steps(&witness);
    let mut rows = Vec::new();
    let mut failures = Vec::new();

    for fold_step in fold_steps {
        for log_blowup in [1, 2, 3] {
            for pow_bits in [0, 10, 20] {
                for log_last_layer in [1, 5] {
                    let case = Case {
                        pow_bits,
                        log_blowup,
                        log_last_layer,
                        n_queries: min_queries(pow_bits, log_blowup),
                        fold_step,
                    };
                    match run_case(draft, &witness, case, samples) {
                        Ok(row) => rows.push(row),
                        Err(error) => failures.push((case, error)),
                    }
                }
            }
        }
    }

    print_csv(&rows, &failures);
    print_pareto(&rows);
    print_recommendation(&rows);
}

fn supported_fold_steps(witness: &eu_id_prover::PipelineWitness) -> Vec<u32> {
    if env::var("FRI_SWEEP_SKIP_FOLD_PROBE").ok().as_deref() == Some("1") {
        eprintln!("fold_step=2 probe skipped by FRI_SWEEP_SKIP_FOLD_PROBE=1; using fold_step=1");
        return vec![1];
    }

    let draft = witness
        .p256_draft
        .as_ref()
        .expect("valid_over_18 has a valid P256 draft");
    let probe = Case {
        pow_bits: CURRENT_POW_BITS,
        log_blowup: CURRENT_LOG_BLOWUP,
        log_last_layer: CURRENT_LAST_LAYER,
        n_queries: min_queries(CURRENT_POW_BITS, CURRENT_LOG_BLOWUP),
        fold_step: 2,
    };

    match catch_unwind(AssertUnwindSafe(|| run_sample(draft, witness, probe))) {
        Ok(Ok(_)) => {
            eprintln!("fold_step=2 probe verified; including fold_step axis [1, 2]");
            vec![1, 2]
        }
        Ok(Err(error)) => {
            eprintln!("fold_step=2 probe failed: {error}; using fold_step=1");
            vec![1]
        }
        Err(_) => {
            eprintln!("fold_step=2 probe panicked/asserted; using fold_step=1");
            vec![1]
        }
    }
}

fn run_case(
    draft: &stwo_p256::proof::P256ProofDraft,
    witness: &eu_id_prover::PipelineWitness,
    case: Case,
    samples: usize,
) -> Result<Row, String> {
    let mut prove_timings = Vec::with_capacity(samples);
    let mut verify_timings = Vec::with_capacity(samples);
    let mut proof_bytes = None;
    let mut composition_ms = 0.0;

    for _ in 0..samples {
        let sample = run_sample(draft, witness, case)?;
        prove_timings.push(sample.prove_ms);
        verify_timings.push(sample.verify_ms);
        proof_bytes = Some(sample.proof_bytes);
        composition_ms += sample.composition_ms;
    }

    prove_timings.sort_by(f64::total_cmp);
    verify_timings.sort_by(f64::total_cmp);
    Ok(Row {
        case,
        prove_ms: prove_timings[prove_timings.len() / 2],
        verify_ms: verify_timings[verify_timings.len() / 2],
        proof_bytes: proof_bytes.unwrap_or(0),
        composition_ms: composition_ms / samples as f64,
        verified: true,
    })
}

struct Sample {
    prove_ms: f64,
    verify_ms: f64,
    proof_bytes: usize,
    composition_ms: f64,
}

fn run_sample(
    draft: &stwo_p256::proof::P256ProofDraft,
    witness: &eu_id_prover::PipelineWitness,
    case: Case,
) -> Result<Sample, String> {
    let collector = SpanAccumulator::default();
    let subscriber = Registry::default().with(collector.clone());
    let _guard = tracing::subscriber::set_default(subscriber);

    let prove_start = Instant::now();
    let (proof, _) = prove_with_column_breakdown_and_config(
        draft,
        &witness.sha_witness,
        witness.sha_log_n_rows,
        witness.sha_group_width,
        &witness.age_public,
        &witness.age_dob,
        &witness.nat_public,
        &witness.nat_private,
        pcs_config(case),
    )
    .map_err(|error| format!("{error:?}"))?;
    let prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;

    let expected = proof.p256_instances().to_vec();
    let verify_start = Instant::now();
    verify_with_config(&proof, &expected, pcs_config(case))
        .map_err(|error| format!("{error:?}"))?;
    let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;

    let proof_bytes = bincode::serialize(&proof)
        .map_err(|error| error.to_string())?
        .len();
    let composition_ms = span_ms(&collector.export_csv(), "CompositionPolynomialGeneration");

    Ok(Sample {
        prove_ms,
        verify_ms,
        proof_bytes,
        composition_ms,
    })
}

fn pcs_config(case: Case) -> PcsConfig {
    PcsConfig {
        pow_bits: case.pow_bits,
        fri_config: FriConfig::new(
            case.log_last_layer,
            case.log_blowup,
            case.n_queries,
            case.fold_step,
        ),
        lifting_log_size: None,
    }
}

fn min_queries(pow_bits: u32, log_blowup: u32) -> usize {
    let remaining = 128u32.saturating_sub(pow_bits);
    if remaining == 0 {
        0
    } else {
        remaining.div_ceil(log_blowup) as usize
    }
}

fn span_ms(csv: &str, label: &str) -> f64 {
    csv.lines()
        .skip(1)
        .filter_map(|line| line.split_once(','))
        .find_map(|(class, value)| {
            if class == label {
                value.parse::<f64>().ok()
            } else {
                None
            }
        })
        .unwrap_or(0.0)
}

fn print_csv(rows: &[Row], failures: &[(Case, String)]) {
    println!("status,pow_bits,log_blowup,n_queries,log_last_layer,fold_step,prove_ms,verify_ms,total_ms,proof_bytes,composition_ms,verified,error");
    for row in rows {
        let c = row.case;
        println!(
            "ok,{},{},{},{},{},{:.3},{:.3},{:.3},{},{:.3},{},",
            c.pow_bits,
            c.log_blowup,
            c.n_queries,
            c.log_last_layer,
            c.fold_step,
            row.prove_ms,
            row.verify_ms,
            row.prove_ms + row.verify_ms,
            row.proof_bytes,
            row.composition_ms,
            row.verified
        );
    }
    for (case, error) in failures {
        println!(
            "err,{},{},{},{},{},,,,,,,{}",
            case.pow_bits,
            case.log_blowup,
            case.n_queries,
            case.log_last_layer,
            case.fold_step,
            error.replace(',', ";")
        );
    }
}

fn print_pareto(rows: &[Row]) {
    let mut pareto: Vec<_> = rows.iter().filter(|row| is_pareto(row, rows)).collect();
    pareto.sort_by(|a, b| {
        a.proof_bytes
            .cmp(&b.proof_bytes)
            .then_with(|| a.prove_ms.total_cmp(&b.prove_ms))
    });

    println!("\n| pow | blowup | queries | last | fold | prove ms | verify ms | proof bytes | composition ms | current |");
    println!("|---:|---:|---:|---:|---:|---:|---:|---:|---:|:---:|");
    for row in pareto {
        let c = row.case;
        println!(
            "| {} | {} | {} | {} | {} | {:.3} | {:.3} | {} | {:.3} | {} |",
            c.pow_bits,
            c.log_blowup,
            c.n_queries,
            c.log_last_layer,
            c.fold_step,
            row.prove_ms,
            row.verify_ms,
            row.proof_bytes,
            row.composition_ms,
            if is_current(c) { "yes" } else { "" }
        );
    }
}

fn print_recommendation(rows: &[Row]) {
    let Some(current) = rows.iter().find(|row| is_current(row.case)) else {
        eprintln!("current production config row was not produced");
        return;
    };
    let Some(recommended) = rows
        .iter()
        .filter(|row| is_pareto(row, rows))
        .min_by(|a, b| {
            a.proof_bytes
                .cmp(&b.proof_bytes)
                .then_with(|| a.prove_ms.total_cmp(&b.prove_ms))
        })
    else {
        eprintln!("no successful sweep rows");
        return;
    };

    println!(
        "\nrecommendation: pow_bits={}, log_blowup={}, n_queries={}, log_last_layer={}, fold_step={}",
        recommended.case.pow_bits,
        recommended.case.log_blowup,
        recommended.case.n_queries,
        recommended.case.log_last_layer,
        recommended.case.fold_step
    );
    println!(
        "current_vs_recommended: current_prove_ms={:.3}, recommended_prove_ms={:.3}, current_verify_ms={:.3}, recommended_verify_ms={:.3}, current_bytes={}, recommended_bytes={}",
        current.prove_ms,
        recommended.prove_ms,
        current.verify_ms,
        recommended.verify_ms,
        current.proof_bytes,
        recommended.proof_bytes
    );
}

fn is_pareto(candidate: &Row, rows: &[Row]) -> bool {
    !rows.iter().any(|other| {
        other.proof_bytes <= candidate.proof_bytes
            && other.prove_ms <= candidate.prove_ms
            && (other.proof_bytes < candidate.proof_bytes || other.prove_ms < candidate.prove_ms)
    })
}

fn is_current(case: Case) -> bool {
    case.pow_bits == CURRENT_POW_BITS
        && case.log_blowup == CURRENT_LOG_BLOWUP
        && case.log_last_layer == CURRENT_LAST_LAYER
        && case.fold_step == CURRENT_FOLD_STEP
}
