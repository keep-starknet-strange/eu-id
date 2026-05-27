#![allow(dead_code)]

use predicates::{nat as nat_predicate, NatPrivateInput, NatProof, NatPublicInput};

use super::common::{get_flag, DEFAULT_PROOF_PATH};

pub fn prove_usage() -> ! {
    eprintln!("usage: prove nat --nationality CODE[,CODE...] --acceptable CODE[,CODE...] [--output PATH]");
    eprintln!("  --nationality  prover's ISO 3166-1 numeric codes (comma-separated, required)");
    eprintln!("  --acceptable   acceptable nationality codes (comma-separated, required)");
    eprintln!("  --output       proof output path, default {DEFAULT_PROOF_PATH}");
    std::process::exit(1);
}

pub fn verify_usage() -> ! {
    eprintln!("usage: verify nat [--input PATH]");
    eprintln!("  --input  proof file path, default {DEFAULT_PROOF_PATH}");
    std::process::exit(1);
}

pub fn prove(args: &[String], output: &str) {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        prove_usage();
    }

    let nationality = get_flag(args, "--nationality")
        .map(|s| parse_codes(s))
        .unwrap_or_else(|| {
            eprintln!("--nationality is required");
            prove_usage()
        });

    let acceptable = get_flag(args, "--acceptable")
        .map(|s| parse_codes(s))
        .unwrap_or_else(|| {
            eprintln!("--acceptable is required");
            prove_usage()
        });

    let public = NatPublicInput::new(acceptable);
    let private = NatPrivateInput { nationalities: nationality };

    let proof = nat_predicate::prove_nationality(&public, &private).unwrap_or_else(|e| {
        eprintln!("prove failed: {e}");
        std::process::exit(1)
    });

    std::fs::write(output, serialize_proof(&proof)).unwrap_or_else(|e| {
        eprintln!("failed to write proof: {e}");
        std::process::exit(1)
    });

    println!("proof written to {output}");
}

pub fn verify(args: &[String], input: &str) {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        verify_usage();
    }

    let bytes = std::fs::read(input).unwrap_or_else(|_| {
        eprintln!("no proof file found at {input}, run `prove` first");
        std::process::exit(1);
    });

    let proof = deserialize_proof(&bytes).unwrap_or_else(|e| {
        eprintln!("failed to deserialize proof: {e}");
        std::process::exit(1)
    });

    nat_predicate::verify_nationality(&proof).unwrap_or_else(|e| {
        eprintln!("verify failed: {e}");
        std::process::exit(1)
    });

    println!("verified ok");
}

fn parse_codes(s: &str) -> Vec<u32> {
    s.split(',')
        .map(|part| {
            part.trim().parse::<u32>().unwrap_or_else(|_| {
                eprintln!("invalid nationality code '{part}', expected an ISO 3166-1 numeric code");
                std::process::exit(1)
            })
        })
        .collect()
}

fn serialize_proof(proof: &NatProof) -> Vec<u8> {
    bincode::serialize(proof).unwrap()
}

fn deserialize_proof(bytes: &[u8]) -> Result<NatProof, Box<dyn std::error::Error>> {
    Ok(bincode::deserialize(bytes)?)
}
