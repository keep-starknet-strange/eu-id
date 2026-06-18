//! `eu-id` — prove / verify a bound identity proof against a fixture credential.
//!
//! Demonstrates the relying-party API ([`eu_id_prover::prove_identity`] /
//! [`eu_id_prover::verify_identity`]) end-to-end, persisting the combined proof
//! between the two steps:
//!
//! ```text
//! eu-id prove  --fixture valid_over_18 --output proof.bin
//! eu-id verify --fixture valid_over_18 --input  proof.bin
//! eu-id list
//! ```
//!
//! `prove` signs the fixture's credential with the built-in **demo issuer** and
//! the fixture's policy, then writes the bincode-serialized proof. `verify`
//! rebuilds the public statement `{ issuer Q, policy }` *independently* of the
//! proof and checks the proof against it.
//!
//! By default `verify` uses the demo issuer's key and the fixture's policy, so an
//! honest proof verifies. The override flags perturb the *expected* statement to
//! show caller-argument binding — a mismatched statement is rejected before the
//! STARK check:
//!
//! ```text
//! eu-id verify --fixture valid_over_18 --min-age 21      # AgePolicyMismatch
//! eu-id verify --fixture valid_over_18 --accept 392      # NatPolicyMismatch
//! eu-id verify --fixture valid_over_18 --issuer other    # IssuerKeyMismatch
//! ```
//!
//! The issuer is always one of two deterministic demo keys; real issuer keys,
//! custom credentials, and reference-date overrides are follow-on work.

use eu_id_prover::fixtures::{self, Fixture};
use eu_id_prover::generator::IssuerKey;
use eu_id_prover::{prove_identity, verify_identity, AffinePoint, Policy, Proof, PublicStatement};

const DEFAULT_PROOF_PATH: &str = "proof.bin";

/// A second deterministic demo key, distinct from [`IssuerKey::demo`] — used by
/// `--issuer other` to demonstrate the issuer-key mismatch path.
const OTHER_ISSUER_SEED: [u8; 32] = [9u8; 32];

fn get_flag<'a>(args: &'a [String], flag: &str) -> Option<&'a str> {
    args.windows(2)
        .find(|w| w[0] == flag)
        .map(|w| w[1].as_str())
}

fn usage() -> ! {
    eprintln!("usage: eu-id <command> [flags]");
    eprintln!("commands:");
    eprintln!("  prove  --fixture NAME [--output PATH]");
    eprintln!("         prove a bound identity proof for a fixture credential");
    eprintln!("  verify --fixture NAME [--input PATH] [--issuer demo|other] [--min-age N] [--accept a,b,c]");
    eprintln!("         verify a proof against the fixture's public statement;");
    eprintln!("         the override flags perturb the expected statement to show rejection");
    eprintln!("  list   list the available fixtures");
    eprintln!("proof path defaults to {DEFAULT_PROOF_PATH}");
    std::process::exit(1);
}

/// Resolve a fixture by name, or list the choices and exit.
fn find_fixture(name: &str) -> Fixture {
    fixtures::all()
        .into_iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| {
            eprintln!("unknown fixture '{name}'. available:");
            for f in fixtures::all() {
                eprintln!("  {}", f.name);
            }
            std::process::exit(1);
        })
}

fn require_fixture(args: &[String]) -> Fixture {
    let name = get_flag(args, "--fixture").unwrap_or_else(|| {
        eprintln!("--fixture is required");
        usage()
    });
    find_fixture(name)
}

fn cmd_prove(args: &[String]) {
    let fixture = require_fixture(args);
    let output = get_flag(args, "--output").unwrap_or(DEFAULT_PROOF_PATH);

    println!(
        "proving fixture '{}': {}",
        fixture.name, fixture.description
    );
    let proof = prove_identity(
        &fixture.signed.credential,
        &IssuerKey::demo(),
        &fixture.policy,
    )
    .unwrap_or_else(|e| {
        // A false statement (e.g. under-age) is rejected at witness
        // generation — the prover cannot attest it.
        eprintln!("cannot prove this credential: {e:?}");
        std::process::exit(1);
    });

    let bytes = bincode::serialize(&proof).unwrap_or_else(|e| {
        eprintln!("failed to serialize proof: {e}");
        std::process::exit(1);
    });
    std::fs::write(output, &bytes).unwrap_or_else(|e| {
        eprintln!("failed to write proof: {e}");
        std::process::exit(1);
    });
    println!("proof written to {output} ({} bytes)", bytes.len());
}

/// Build the relying party's expected statement: the fixture's policy with any
/// `--min-age` / `--accept` overrides, paired with the chosen issuer key.
fn expected_statement(args: &[String], fixture: &Fixture) -> PublicStatement {
    let mut policy: Policy = fixture.policy.clone();

    if let Some(m) = get_flag(args, "--min-age") {
        policy.min_age_years = m.parse().unwrap_or_else(|_| {
            eprintln!("--min-age must be a non-negative integer");
            std::process::exit(1);
        });
    }
    if let Some(list) = get_flag(args, "--accept") {
        policy.accepted_nationalities = list
            .split(',')
            .map(|s| {
                s.trim().parse::<u32>().unwrap_or_else(|_| {
                    eprintln!("--accept must be a comma-separated list of integers");
                    std::process::exit(1);
                })
            })
            .collect();
    }

    let issuer_key: AffinePoint = match get_flag(args, "--issuer") {
        None | Some("demo") => IssuerKey::demo().public_key(),
        Some("other") => IssuerKey::from_seed(&OTHER_ISSUER_SEED).public_key(),
        Some(other) => {
            eprintln!("--issuer must be 'demo' or 'other', got '{other}'");
            std::process::exit(1);
        }
    };

    PublicStatement::new(issuer_key, policy)
}

fn cmd_verify(args: &[String]) {
    let fixture = require_fixture(args);
    let input = get_flag(args, "--input").unwrap_or(DEFAULT_PROOF_PATH);

    let bytes = std::fs::read(input).unwrap_or_else(|_| {
        eprintln!("no proof file at {input}; run `eu-id prove` first");
        std::process::exit(1);
    });
    let proof: Proof = bincode::deserialize(&bytes).unwrap_or_else(|e| {
        eprintln!("failed to deserialize proof: {e}");
        std::process::exit(1);
    });

    let statement = expected_statement(args, &fixture);
    match verify_identity(&proof, &statement) {
        Ok(()) => println!(
            "verified ok against fixture '{}' statement (issuer Q + policy)",
            fixture.name
        ),
        Err(e) => {
            eprintln!("verification REJECTED: {e:?}");
            std::process::exit(1);
        }
    }
}

fn cmd_list() {
    println!("fixtures:");
    for f in fixtures::all() {
        println!("  {:<28} {}", f.name, f.description);
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let command = args.first().map(String::as_str).unwrap_or_else(|| usage());
    let rest = &args[1..];
    match command {
        "prove" => cmd_prove(rest),
        "verify" => cmd_verify(rest),
        "list" => cmd_list(),
        "--help" | "-h" => usage(),
        other => {
            eprintln!("unknown command '{other}'");
            usage();
        }
    }
}
