use std::env;
#[cfg(any(target_os = "android", target_os = "linux"))]
use std::fs;
#[cfg(any(target_os = "android", target_os = "linux"))]
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;

use rayon::ThreadPoolBuilder;

const RAYON_NUM_THREADS_ENV: &str = "RAYON_NUM_THREADS";
#[cfg(any(test, target_os = "android", target_os = "linux"))]
const PERFORMANCE_TIER_PERCENT: u128 = 80;
#[cfg(any(test, target_os = "android", target_os = "linux"))]
const WHOLE_PERCENT: u128 = 100;
const FALLBACK_THREAD_COUNT: usize = 1;
const NO_THREAD_OVERRIDE: usize = 0;
const THREAD_POOL_INITIALIZED: usize = usize::MAX;

#[cfg(any(target_os = "android", target_os = "linux"))]
const CPU_SYSFS_ROOT: &str = "/sys/devices/system/cpu";
#[cfg(target_vendor = "apple")]
const PERFORMANCE_CORE_SYSCTL: &[u8] = b"hw.perflevel0.logicalcpu\0";

static THREAD_OVERRIDE_STATE: AtomicUsize = AtomicUsize::new(NO_THREAD_OVERRIDE);
static THREAD_POOL_INITIALIZATION: OnceLock<()> = OnceLock::new();

pub(crate) fn configure(threads: u32) -> bool {
    configure_state(&THREAD_OVERRIDE_STATE, threads)
}

pub(crate) fn initialize() {
    THREAD_POOL_INITIALIZATION.get_or_init(|| {
        let explicit = take_override_and_mark_initialized(&THREAD_OVERRIDE_STATE);
        let environment = env::var(RAYON_NUM_THREADS_ENV).ok();
        let threads = select_thread_count(explicit, environment.as_deref(), detected_thread_count);

        if let Err(error) = ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
        {
            eprintln!(
                "euid-zk-sdk: keeping the existing Rayon global thread pool after initialization failed: {error}"
            );
        }
    });
}

pub(crate) fn current_thread_count() -> Option<usize> {
    THREAD_POOL_INITIALIZATION
        .get()
        .map(|()| rayon::current_num_threads())
}

pub(crate) fn detected_thread_count() -> usize {
    platform_performance_core_count().unwrap_or_else(available_thread_count)
}

fn configure_state(state: &AtomicUsize, threads: u32) -> bool {
    let Ok(threads) = usize::try_from(threads) else {
        return false;
    };
    if threads == 0 || threads > rayon::max_num_threads() {
        return false;
    }

    state
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            (current != THREAD_POOL_INITIALIZED).then_some(threads)
        })
        .is_ok()
}

fn take_override_and_mark_initialized(state: &AtomicUsize) -> Option<usize> {
    match state.swap(THREAD_POOL_INITIALIZED, Ordering::AcqRel) {
        NO_THREAD_OVERRIDE | THREAD_POOL_INITIALIZED => None,
        threads => Some(threads),
    }
}

fn select_thread_count(
    explicit: Option<usize>,
    environment: Option<&str>,
    detect: impl FnOnce() -> usize,
) -> usize {
    explicit
        .filter(|threads| *threads > 0)
        .or_else(|| environment.and_then(parse_thread_count))
        .unwrap_or_else(detect)
}

fn parse_thread_count(value: &str) -> Option<usize> {
    value
        .parse()
        .ok()
        .filter(|threads| *threads > 0 && *threads <= rayon::max_num_threads())
}

#[cfg(any(test, target_os = "android", target_os = "linux"))]
fn classify_performance_tier<I, S>(frequencies: I) -> Option<usize>
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let frequencies = frequencies
        .into_iter()
        .map(|frequency| {
            frequency
                .as_ref()
                .trim()
                .parse::<u64>()
                .ok()
                .filter(|frequency| *frequency > 0)
        })
        .collect::<Option<Vec<_>>>()?;
    let maximum = u128::from(*frequencies.iter().max()?);
    Some(
        frequencies
            .iter()
            .filter(|frequency| {
                u128::from(**frequency) * WHOLE_PERCENT >= maximum * PERFORMANCE_TIER_PERCENT
            })
            .count(),
    )
}

#[cfg(any(target_os = "android", target_os = "linux"))]
fn platform_performance_core_count() -> Option<usize> {
    linux_performance_core_count(Path::new(CPU_SYSFS_ROOT))
}

#[cfg(any(target_os = "android", target_os = "linux"))]
fn linux_performance_core_count(root: &Path) -> Option<usize> {
    let mut frequencies = Vec::new();
    for entry in fs::read_dir(root).ok()? {
        let entry = entry.ok()?;
        let name = entry.file_name();
        let name = name.to_str()?;
        if !is_cpu_directory(name) {
            continue;
        }
        frequencies.push(fs::read_to_string(entry.path().join("cpufreq/cpuinfo_max_freq")).ok()?);
    }
    classify_performance_tier(frequencies)
}

#[cfg(any(target_os = "android", target_os = "linux"))]
fn is_cpu_directory(name: &str) -> bool {
    name.strip_prefix("cpu").is_some_and(|index| {
        !index.is_empty() && index.chars().all(|character| character.is_ascii_digit())
    })
}

#[cfg(target_vendor = "apple")]
fn platform_performance_core_count() -> Option<usize> {
    let mut logical_cpu: libc::c_int = 0;
    let mut value_size = std::mem::size_of_val(&logical_cpu);
    // SAFETY: the NUL-terminated name is static, and both output pointers are
    // valid for `value_size` bytes for the duration of this read-only call.
    let status = unsafe {
        libc::sysctlbyname(
            PERFORMANCE_CORE_SYSCTL.as_ptr().cast(),
            (&mut logical_cpu as *mut libc::c_int).cast(),
            &mut value_size,
            std::ptr::null_mut(),
            0,
        )
    };
    if status != 0 || value_size != std::mem::size_of_val(&logical_cpu) {
        return None;
    }
    usize::try_from(logical_cpu).ok().filter(|count| *count > 0)
}

#[cfg(not(any(target_os = "android", target_os = "linux", target_vendor = "apple")))]
fn platform_performance_core_count() -> Option<usize> {
    None
}

fn available_thread_count() -> usize {
    std::thread::available_parallelism().map_or(FALLBACK_THREAD_COUNT, |count| count.get())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pixel_8_pro_fixture_selects_five_performance_cores() {
        let frequencies = [
            "2910000", "2370000", "2370000", "2370000", "2370000", "1700000", "1700000", "1700000",
            "1700000",
        ];
        assert_eq!(classify_performance_tier(frequencies), Some(5));
    }

    #[test]
    fn heterogeneous_topology_fixtures_select_only_the_fast_tier() {
        let one_plus_three_plus_four = [
            "3000000", "2400000", "2400000", "2400000", "1800000", "1800000", "1800000", "1800000",
        ];
        let two_plus_six = [
            "3000000", "3000000", "2100000", "2100000", "2100000", "2100000", "2100000", "2100000",
        ];
        assert_eq!(classify_performance_tier(one_plus_three_plus_four), Some(4));
        assert_eq!(classify_performance_tier(two_plus_six), Some(2));
    }

    #[test]
    fn uniform_desktop_fixture_keeps_every_core() {
        assert_eq!(classify_performance_tier(["3200000"; 12]), Some(12));
    }

    #[test]
    fn garbage_and_empty_sysfs_fixtures_use_the_fallback() {
        const FALLBACK: usize = 6;
        assert_eq!(
            classify_performance_tier(["not-a-frequency", ""]).unwrap_or(FALLBACK),
            FALLBACK
        );
        assert_eq!(
            classify_performance_tier(std::iter::empty::<&str>()).unwrap_or(FALLBACK),
            FALLBACK
        );
    }

    #[test]
    fn override_precedes_environment_and_detection() {
        assert_eq!(
            select_thread_count(Some(5), Some("9"), || panic!("detection must not run")),
            5
        );
    }

    #[test]
    fn environment_precedes_detection() {
        assert_eq!(
            select_thread_count(None, Some("7"), || panic!("detection must not run")),
            7
        );
    }

    #[test]
    fn invalid_environment_uses_detection() {
        assert_eq!(select_thread_count(None, Some("invalid"), || 4), 4);
        assert_eq!(select_thread_count(None, Some("0"), || 3), 3);
        let too_large = (rayon::max_num_threads() + 1).to_string();
        assert_eq!(select_thread_count(None, Some(&too_large), || 2), 2);
    }

    #[test]
    fn configuration_is_mutable_only_before_initialization() {
        let state = AtomicUsize::new(NO_THREAD_OVERRIDE);
        assert!(!configure_state(&state, 0));
        assert!(configure_state(&state, 4));
        assert!(configure_state(&state, 5));
        assert_eq!(take_override_and_mark_initialized(&state), Some(5));
        assert!(!configure_state(&state, 6));
    }

    #[test]
    fn configuration_rejects_after_the_global_pool_initializes() {
        initialize();
        assert!(!configure(2));
    }
}
