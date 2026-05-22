#![allow(dead_code)]

use predicates::{
    age as age_predicate, AgeCheckStrategy, AgeBitDecompositionProof, AgeProof, AgeRangeCheckProof,
    Date, DateOfBirth, PublicInput,
};
use std::time::{SystemTime, UNIX_EPOCH};

use super::common::{get_flag, DEFAULT_PROOF_PATH};

pub fn prove_usage() -> ! {
    eprintln!("usage: prove age --dob YYYY-MM-DD [--date YYYY-MM-DD] [--min-age N] [--strategy bd|rc] [--output PATH]");
    eprintln!("  --dob       date of birth (required)");
    eprintln!("  --date      current date, defaults to today");
    eprintln!("  --min-age   minimum age in years, default 18");
    eprintln!("  --strategy  bd (bit decomposition) | rc (range check), default rc");
    eprintln!("  --output    proof output path, default {DEFAULT_PROOF_PATH}");
    std::process::exit(1);
}

pub fn verify_usage() -> ! {
    eprintln!("usage: verify age [--strategy bd|rc] [--input PATH]");
    eprintln!("  --strategy  bd (bit decomposition) | rc (range check), default rc");
    eprintln!("  --input     proof file path, default {DEFAULT_PROOF_PATH}");
    std::process::exit(1);
}

pub fn prove(args: &[String], output: &str) {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        prove_usage();
    }

    let dob = get_flag(args, "--dob")
        .map(|s| parse_date(s).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(1) }))
        .unwrap_or_else(|| { eprintln!("--dob is required"); prove_usage() });

    let current = get_flag(args, "--date")
        .map(|s| parse_date(s).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(1) }))
        .unwrap_or_else(today);

    let min_age = get_flag(args, "--min-age")
        .map(|s| s.parse::<u32>().unwrap_or_else(|_| { eprintln!("--min-age must be a number"); std::process::exit(1) }))
        .unwrap_or(18);

    let strategy = get_flag(args, "--strategy")
        .map(|s| parse_strategy(s).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(1) }))
        .unwrap_or(AgeCheckStrategy::RangeCheck);

    let public = PublicInput::new(current, min_age);
    let proof = age_predicate::prove(&public, &DateOfBirth(dob), strategy)
        .unwrap_or_else(|e| { eprintln!("prove failed: {e}"); std::process::exit(1) });

    std::fs::write(output, serialize_proof(&proof))
        .unwrap_or_else(|e| { eprintln!("failed to write proof: {e}"); std::process::exit(1) });

    println!("proof written to {output}");
}

pub fn verify(args: &[String], input: &str) {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        verify_usage();
    }

    let strategy = get_flag(args, "--strategy")
        .map(|s| parse_strategy(s).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(1) }))
        .unwrap_or(AgeCheckStrategy::RangeCheck);

    let bytes = std::fs::read(input).unwrap_or_else(|_| {
        eprintln!("no proof file found at {input}, run `prove` first");
        std::process::exit(1);
    });

    let proof = deserialize_proof(&bytes, strategy)
        .unwrap_or_else(|e| { eprintln!("failed to deserialize proof: {e}"); std::process::exit(1) });

    age_predicate::verify(&proof)
        .unwrap_or_else(|e| { eprintln!("verify failed: {e}"); std::process::exit(1) });

    println!("verified ok");
}

// https://howardhinnant.github.io/date_algorithms.html#civil_from_days
fn today() -> Date {
    let days = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs()
        / 86400;
    let z = days as i64 + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = (z - era * 146097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    Date { year: y as u32, month: m as u32, day: d as u32 }
}

fn parse_date(s: &str) -> Result<Date, String> {
    let parts: Vec<&str> = s.splitn(3, '-').collect();
    if parts.len() != 3 {
        return Err(format!("expected YYYY-MM-DD, got '{s}'"));
    }
    let year = parts[0].parse::<u32>().map_err(|_| format!("invalid year in '{s}'"))?;
    let month = parts[1].parse::<u32>().map_err(|_| format!("invalid month in '{s}'"))?;
    let day = parts[2].parse::<u32>().map_err(|_| format!("invalid day in '{s}'"))?;
    Ok(Date { year, month, day })
}

fn parse_strategy(s: &str) -> Result<AgeCheckStrategy, String> {
    match s {
        "bd" => Ok(AgeCheckStrategy::BitDecomposition),
        "rc" => Ok(AgeCheckStrategy::RangeCheck),
        other => Err(format!("unknown strategy '{other}', expected: bd, rc")),
    }
}

fn serialize_proof(proof: &AgeProof) -> Vec<u8> {
    match proof {
        AgeProof::BitDecomposition(p) => bincode::serialize(p).unwrap(),
        AgeProof::RangeCheck(p) => bincode::serialize(p).unwrap(),
    }
}

fn deserialize_proof(
    bytes: &[u8],
    strategy: AgeCheckStrategy,
) -> Result<AgeProof, Box<dyn std::error::Error>> {
    match strategy {
        AgeCheckStrategy::BitDecomposition => {
            let p: AgeBitDecompositionProof = bincode::deserialize(bytes)?;
            Ok(AgeProof::BitDecomposition(p))
        }
        AgeCheckStrategy::RangeCheck => {
            let p: AgeRangeCheckProof = bincode::deserialize(bytes)?;
            Ok(AgeProof::RangeCheck(p))
        }
    }
}
