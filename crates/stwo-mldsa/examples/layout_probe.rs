//! Layout census for the S1 composition: the shared keccak SERVICE (hosting
//! one instance's four sponge jobs) + ONE ML-DSA-65 statement instance.
//! Column counts and cell totals per tree, grouped by log_size. Run:
//! `cargo run -p stwo-mldsa --example layout_probe --release`

use air_core::{Air, TreeLayout};
use ml_dsa::signature::{Keypair, Signer};
use ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsa65, SigningKey};
use stwo::core::fields::qm31::SecureField;
use stwo_keccak::relations::SharedKeccakRelations;
use stwo_keccak::service::{service_claimed_sums_len, KeccakServiceVerifier};
use stwo_mldsa::reference::encoding::{pk_decode, sig_decode};
use stwo_mldsa::reference::sponge::shake256;
use stwo_mldsa::statement::keccak_job_shapes;
use stwo_mldsa::witness::generate_witness;
use stwo_mldsa::MlDsaVerifyInput;

fn dump(label: &str, layout: &TreeLayout) -> u64 {
    println!("──── {label} ────");
    for (name, cols) in [
        ("preprocessed", &layout.preprocessed),
        ("trace", &layout.trace),
        ("interaction", &layout.interaction),
    ] {
        let mut by_log: std::collections::BTreeMap<u32, usize> = Default::default();
        for &l in cols.iter() {
            *by_log.entry(l).or_default() += 1;
        }
        let cells: u64 = cols.iter().map(|&l| 1u64 << l).sum();
        println!(
            "== {name}: {} cols, {:.2} M cells",
            cols.len(),
            cells as f64 / 1e6
        );
        for (l, n) in by_log {
            println!(
                "   log {l:>2}: {n:>5} cols  ({:.2} M cells)",
                (n as u64 * (1u64 << l)) as f64 / 1e6
            );
        }
    }
    let total: u64 = [&layout.preprocessed, &layout.trace, &layout.interaction]
        .iter()
        .flat_map(|v| v.iter())
        .map(|&l| 1u64 << l)
        .sum();
    let cols: usize = layout.preprocessed.len() + layout.trace.len() + layout.interaction.len();
    println!(
        "== {label} TOTAL: {cols} cols, {:.2} M cells",
        total as f64 / 1e6
    );
    total
}

fn main() {
    let msg = vec![0xabu8; 2048]; // issuer-Sig_structure-sized message
    let sk = SigningKey::<MlDsa65>::from_seed(&[7u8; 32].into());
    let vk = sk.verifying_key();
    let sig = sk.sign(&msg);
    let vk_bytes: EncodedVerifyingKey<MlDsa65> = vk.encode();
    let sig_bytes: EncodedSignature<MlDsa65> = sig.encode();
    let pk = pk_decode(vk_bytes.as_slice()).unwrap();
    let sp = sig_decode(sig_bytes.as_slice()).unwrap();
    let (tr_vec, _) = shake256(&[vk_bytes.as_slice()], 64);
    let mut tr = [0u8; 64];
    tr.copy_from_slice(&tr_vec);
    let input = MlDsaVerifyInput::from_decoded(&pk, &sp, tr, msg);

    let witness = generate_witness(&input).unwrap();
    let sib_stream_len = stwo_mldsa::sampleinball::stream_len(&witness);
    let sib_squeezed_len = witness.sponge.sample_in_ball_squeezed.len();

    // Instance layout (S1: no sponges/keccak/round/tables — those live in the
    // service).
    let instance = stwo_mldsa::statement::debug_layout(&input, sib_stream_len, sib_squeezed_len);
    let instance_cells = dump("mldsa instance", &instance);
    let instance_cols =
        instance.preprocessed.len() + instance.trace.len() + instance.interaction.len();

    // Service layout for this ONE instance's four sponge jobs (pkHash, µ, c̃, SIB).
    let jobs = keccak_job_shapes(input.message.len(), sib_stream_len, 0);
    let service = KeccakServiceVerifier::new(
        jobs,
        vec![SecureField::default(); service_claimed_sums_len()],
        SharedKeccakRelations::new(),
    );
    let service_layout = service.layout();
    let service_cells = dump("keccak service", &service_layout);
    let service_cols = service_layout.preprocessed.len()
        + service_layout.trace.len()
        + service_layout.interaction.len();

    println!(
        "== COMPOSITION TOTAL: {} cols, {:.2} M cells (service + 1 instance)",
        instance_cols + service_cols,
        (instance_cells + service_cells) as f64 / 1e6
    );
}
