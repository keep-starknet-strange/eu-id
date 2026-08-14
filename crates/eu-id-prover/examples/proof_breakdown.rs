//! Where the V8 mdoc identity proof spends its bytes.
//!
//! Proves the demo fixture and prints the byte breakdown, largest bucket first.
//! The buckets partition the raw serialized proof exactly — the same bytes the
//! SDK compresses into the transport envelope.
//!
//! `cargo run -p eu-id-prover --example proof_breakdown --release`

use eu_id_prover::mdoc;

fn main() {
    let fixture = mdoc::demo_mdoc_circuit_fixture();
    let (proof, _) = eu_id_prover::prove_mdoc(
        &fixture.document,
        &fixture.request,
        fixture.statement.policy.clone(),
    )
    .expect("demo mdoc proves");
    let breakdown =
        mdoc::mdoc_proof_byte_breakdown(&proof, &fixture.statement).expect("byte breakdown");

    /// Shared and blob buckets own no columns, so their detail is `None`.
    struct Row {
        label: String,
        bytes: usize,
        detail: Option<ModuleDetail>,
    }
    struct ModuleDetail {
        oods: usize,
        queried: usize,
        columns: usize,
    }

    let mut rows: Vec<Row> = breakdown
        .modules
        .iter()
        .map(|module| Row {
            label: module.label.clone(),
            bytes: module.total(),
            detail: Some(ModuleDetail {
                oods: module.oods_sampled_values,
                queried: module.queried_values,
                columns: module.columns,
            }),
        })
        .collect();
    let shared = &breakdown.shared;
    rows.extend(
        [
            ("[shared] fri_proof", shared.fri_proof),
            ("[shared] trace_decommitments", shared.trace_decommitments),
            (
                "[shared] composition oods",
                shared.composition_oods_sampled_values,
            ),
            (
                "[shared] composition queried",
                shared.composition_queried_values,
            ),
            ("[shared] commitment_roots", shared.commitment_roots),
            ("[shared] pcs_config", shared.pcs_config),
            ("[shared] proof_of_work", shared.proof_of_work),
            ("[blob] coprocessor_bundle", breakdown.coprocessor_bundle),
            ("framing/other", breakdown.framing_other),
        ]
        .into_iter()
        .map(|(label, bytes)| Row {
            label: label.to_string(),
            bytes,
            detail: None,
        }),
    );
    rows.sort_by(|left, right| {
        right
            .bytes
            .cmp(&left.bytes)
            .then_with(|| left.label.cmp(&right.label))
    });

    let total = breakdown.proof_bytes;
    let percent = |bytes: usize| 100.0 * bytes as f64 / total as f64;
    println!(
        "V8 mdoc identity proof: {total} raw serialized bytes ({:.2} MiB)",
        total as f64 / (1024.0 * 1024.0),
    );
    println!();
    println!(
        "{:<40} {:>10} {:>7} {:>10} {:>10} {:>5}",
        "bucket", "bytes", "%", "oods", "queried", "cols",
    );
    println!("{}", "-".repeat(86));
    for Row {
        label,
        bytes,
        detail,
    } in &rows
    {
        match detail {
            Some(detail) => println!(
                "{label:<40} {bytes:>10} {:>6.2}% {:>10} {:>10} {:>5}",
                percent(*bytes),
                detail.oods,
                detail.queried,
                detail.columns,
            ),
            None => println!(
                "{label:<40} {bytes:>10} {:>6.2}% {:>10} {:>10} {:>5}",
                percent(*bytes),
                "-",
                "-",
                "-",
            ),
        }
    }
    println!("{}", "-".repeat(86));
    println!(
        "{:<40} {:>10} {:>6.2}%",
        "TOTAL",
        breakdown.attributed_bytes(),
        percent(breakdown.attributed_bytes()),
    );
    assert_eq!(
        breakdown.attributed_bytes(),
        total,
        "byte buckets do not partition the serialized proof",
    );
}
