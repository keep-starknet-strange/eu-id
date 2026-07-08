//! Shape-gate probe (M7): dump every mdoc module's committed TreeLayout on the
//! P-256 demo fixture. Diffed against the pre-M7 baseline to prove the P-256
//! proof shape is byte-identical after the ML-DSA integration.
use eu_id_prover::mdoc::demo_mdoc_module_shapes;
fn main() {
    let shapes = demo_mdoc_module_shapes().expect("shapes");
    for s in &shapes {
        println!("MODULE {}", s.name);
        println!("  preprocessed {:?}", s.layout.preprocessed);
        println!("  trace {:?}", s.layout.trace);
        println!("  interaction {:?}", s.layout.interaction);
        for c in &s.components {
            println!(
                "  COMPONENT {} log_size={} pre={} trace={} inter={}",
                c.name, c.log_size, c.preprocessed_columns, c.trace_columns, c.interaction_columns
            );
        }
    }
}
