use std::path::PathBuf;
use std::process::ExitCode;

use eu_id_prover::ts13_artifact::{generate_from_json, GenerationMode};

const DEFAULT_INPUT: &str = "artifacts/ts13-demo-v1/generation-input-v1.json";

struct Arguments {
    workspace: PathBuf,
    input: PathBuf,
    mode: GenerationMode,
}

fn usage() -> &'static str {
    "usage: ts13_demo_artifact [--workspace PATH] [--input PATH] [--check]"
}

fn parse_arguments() -> Result<Arguments, String> {
    let mut workspace = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    workspace.pop();
    workspace.pop();
    let mut input = None;
    let mut mode = GenerationMode::Write;
    let mut arguments = std::env::args().skip(1);

    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--workspace" => {
                workspace = arguments
                    .next()
                    .map(PathBuf::from)
                    .ok_or_else(|| "--workspace requires a path".to_owned())?;
            }
            "--input" => {
                input = Some(
                    arguments
                        .next()
                        .map(PathBuf::from)
                        .ok_or_else(|| "--input requires a path".to_owned())?,
                );
            }
            "--check" => mode = GenerationMode::Check,
            "--help" | "-h" => return Err(usage().to_owned()),
            _ => return Err(format!("unknown argument {argument:?}; {}", usage())),
        }
    }

    let input = input.unwrap_or_else(|| workspace.join(DEFAULT_INPUT));
    Ok(Arguments {
        workspace,
        input,
        mode,
    })
}

fn run() -> Result<(), String> {
    let arguments = parse_arguments()?;
    let result = generate_from_json(&arguments.workspace, &arguments.input, arguments.mode)
        .map_err(|error| error.to_string())?;
    println!(
        "TS13 circuit artifact {} (hash {}, V4 body capacity {} bytes)",
        match arguments.mode {
            GenerationMode::Write => "generated",
            GenerationMode::Check => "matches",
        },
        result.circuit_hash,
        result.proof_body_capacity
    );
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("ts13_demo_artifact: {error}");
            ExitCode::FAILURE
        }
    }
}
