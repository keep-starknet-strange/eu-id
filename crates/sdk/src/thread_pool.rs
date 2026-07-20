use std::env;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;

use rayon::ThreadPoolBuilder;

const RAYON_NUM_THREADS_ENV: &str = "RAYON_NUM_THREADS";
const FALLBACK_THREAD_COUNT: usize = 1;
const NO_THREAD_OVERRIDE: usize = 0;
const THREAD_POOL_INITIALIZED: usize = usize::MAX;


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
    available_thread_count()
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







fn available_thread_count() -> usize {
    std::thread::available_parallelism().map_or(FALLBACK_THREAD_COUNT, |count| count.get())
}

#[cfg(test)]
mod tests {
    use super::*;




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
