mod age;
mod common;

use common::{get_flag, DEFAULT_PROOF_PATH};

fn usage() -> ! {
    eprintln!("usage: verify <predicate> [predicate-flags] [--input PATH]");
    eprintln!("predicates:");
    eprintln!("  age   verify age predicate (run `verify age --help` for flags)");
    std::process::exit(1);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let predicate = args.first().map(String::as_str).unwrap_or_else(|| usage());
    let rest = args[1..].to_vec();
    let input = get_flag(&rest, "--input").unwrap_or(DEFAULT_PROOF_PATH);

    match predicate {
        "age" => age::verify(&rest, input),
        "--help" | "-h" => usage(),
        other => {
            eprintln!("unknown predicate '{other}'");
            usage();
        }
    }
}
