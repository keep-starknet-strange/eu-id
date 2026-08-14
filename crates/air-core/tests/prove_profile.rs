//! Per-phase prove profile demo: run a small real prove with the sampler off and
//! then armed, and check the phase x {ms, peak_rss_mib} table it produces.

#![cfg(feature = "prove-profile")]

use air_core::prove_profiled;
use predicates::{AgeRangeCheck, Date, DateOfBirth, PredicateProver, PublicInput};
use stwo::core::pcs::PcsConfig;

/// Phase count of the printed table, excluding the `total` row.
const PHASE_ROWS: usize = 11;

/// The sampler's tick. A phase shorter than one tick can legitimately record no
/// sample, so only longer phases are required to report a peak.
const SAMPLER_TICK_MS: f64 = 10.0;

/// The one phase with no work in this fixture: the age module publishes no
/// post-interaction (GKR) transcript block.
const EMPTY_PHASE: &str = "post_interaction";

/// One small real prove: the standalone age range-check module.
fn profile_one_age_prove() -> air_core::StarkProveProfile {
    let public = PublicInput::new(
        Date {
            year: 2026,
            month: 8,
            day: 4,
        },
        18,
    );
    let dob = DateOfBirth(Date {
        year: 1990,
        month: 7,
        day: 15,
    });
    let mut prover = AgeRangeCheck::new(PcsConfig::default())
        .prover(&public, &dob)
        .expect("age prover builds");

    let (_proof, profile) = prove_profiled(&mut [&mut prover], PcsConfig::default())
        .expect("the age module proves standalone");
    profile
}

#[test]
fn prove_profile_reports_wall_time_and_peak_rss_per_phase() {
    // Unarmed first: timing is always collected, but no sampler thread runs and
    // no peaks are reported. This is the zero-overhead default path.
    let unarmed = profile_one_age_prove();
    assert!(
        unarmed.total > 0.0,
        "timing is collected without the env flag: {unarmed:?}"
    );
    assert!(
        unarmed.peak_rss_mib.is_empty(),
        "no peaks may be reported unless EUID_PROVE_PROFILE=1: {:?}",
        unarmed.peak_rss_mib
    );
    assert!(
        unarmed.to_string().contains("peak_rss_mib"),
        "the table still renders without the sampler"
    );

    // The sampler reads this at `prove_profiled` entry, so set it before proving.
    // SAFETY: single-threaded test body, before any sampler thread exists.
    unsafe {
        std::env::set_var("EUID_PROVE_PROFILE", "1");
    }
    let profile = profile_one_age_prove();

    let table = profile.to_string();
    println!("{table}");

    // All phases in table order, so the peak-RSS vector lines up by index.
    let phases = [
        ("twiddles", profile.twiddles),
        ("tree0_write", profile.tree0_write),
        ("tree0_commit", profile.tree0_commit),
        ("tree1_write", profile.tree1_write),
        ("tree1_commit", profile.tree1_commit),
        ("draw_relations", profile.draw_relations),
        ("tree2_write", profile.tree2_write),
        ("tree2_commit", profile.tree2_commit),
        ("post_interaction", profile.post_interaction),
        ("build_components", profile.build_components),
        ("engine_prove", profile.engine_prove),
    ];
    assert_eq!(phases.len(), PHASE_ROWS);

    // Every phase that does work for this module must be timed. The age module
    // publishes no GKR block, so `post_interaction` is genuinely empty here.
    for (label, ms) in phases {
        if label == EMPTY_PHASE {
            continue;
        }
        assert!(ms > 0.0, "phase {label} reported no duration: {profile:?}");
    }
    assert!(
        profile.total >= profile.engine_prove,
        "total must cover the engine prove: {profile:?}"
    );

    assert_eq!(
        profile.peak_rss_mib.len(),
        PHASE_ROWS,
        "the armed sampler must report one peak per phase"
    );
    let overall_peak = profile
        .peak_rss_mib
        .iter()
        .copied()
        .max_by(f64::total_cmp)
        .expect("one peak per phase");
    assert!(
        overall_peak > 0.0,
        "the armed sampler recorded no memory at all: {:?}",
        profile.peak_rss_mib
    );
    // Phase tagging: a phase long enough to be sampled must own a reading.
    for ((label, ms), mib) in phases.iter().zip(&profile.peak_rss_mib) {
        if *ms > SAMPLER_TICK_MS {
            assert!(
                *mib > 0.0,
                "phase {label} ran {ms:.3} ms but recorded no peak RSS: {:?}",
                profile.peak_rss_mib
            );
        }
    }

    assert!(!profile.tree1_write_per_module.is_empty());
    assert!(!profile.tree2_write_per_module.is_empty());

    for label in ["phase", "peak_rss_mib", "engine_prove", "total"] {
        assert!(table.contains(label), "table is missing {label}: {table}");
    }
}
