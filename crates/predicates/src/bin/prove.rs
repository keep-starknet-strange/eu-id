mod age;
mod common;
mod nat;

use common::{get_flag, DEFAULT_PROOF_PATH};

fn usage() -> ! {
    eprintln!("usage: prove <predicate> [predicate-flags] [--output PATH]");
    eprintln!("predicates:");
    eprintln!("  age   prove age predicate (run `prove age --help` for flags)");
    eprintln!("  nat   prove nationality predicate (run `prove nat --help` for flags)");
    std::process::exit(1);
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let predicate = args.first().map(String::as_str).unwrap_or_else(|| usage());
    let rest = args[1..].to_vec();
    let output = get_flag(&rest, "--output").unwrap_or(DEFAULT_PROOF_PATH);

    match predicate {
        "age" => age::prove(&rest, output),
        "nat" => nat::prove(&rest, output),
        "--help" | "-h" => usage(),
        other => {
            eprintln!("unknown predicate '{other}'");
            usage();
        }
    }
}
