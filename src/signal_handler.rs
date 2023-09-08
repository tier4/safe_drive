//! Receive signals on a thread for graceful shutdown.

use crate::{
    helper::InitOnce,
    logger::{pr_info_in, Logger},
    rcl,
    selector::guard_condition::GuardCondition,
};
use once_cell::sync::Lazy;
use parking_lot::{lock_api::MutexGuard, Mutex, RawMutex};
use signal_hook::consts::*;

#[cfg(not(target_os = "windows"))]
use signal_hook::iterator::{Handle, Signals, SignalsInfo};
#[cfg(target_os = "windows")]
use std::sync::Arc;
use std::{
    collections::BTreeMap,
    error::Error,
    fmt::Display,
    sync::atomic::{AtomicBool, Ordering},
    thread::{self, JoinHandle},
};

#[derive(Eq, PartialEq, Ord, PartialOrd)]
struct KeyCond(*const rcl::rcl_guard_condition_t);

unsafe impl Sync for KeyCond {}
unsafe impl Send for KeyCond {}

type ConditionSet = BTreeMap<KeyCond, GuardCondition>;

static INITIALIZER: InitOnce = InitOnce::new();
static GUARD_COND: Lazy<Mutex<ConditionSet>> = Lazy::new(|| Mutex::new(ConditionSet::new()));
#[cfg(not(target_os = "windows"))]
static SIGHDL: Lazy<Mutex<Option<Handle>>> = Lazy::new(|| Mutex::new(None));
static THREAD: Lazy<Mutex<Option<JoinHandle<()>>>> = Lazy::new(|| Mutex::new(None));
#[cfg(not(target_os = "windows"))]
static IS_HALT: AtomicBool = AtomicBool::new(false);
#[cfg(target_os = "windows")]
static IS_HALT: Lazy<Arc<AtomicBool>> = Lazy::new(|| Arc::new(AtomicBool::new(false)));

#[derive(Debug)]
pub struct Signaled;

impl Display for Signaled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Signaled")
    }
}

impl Error for Signaled {}

#[cfg(not(target_os = "windows"))]
pub(crate) fn init() {
    INITIALIZER.init(
        || {
            let signals = Signals::new(&[SIGHUP, SIGTERM, SIGINT, SIGQUIT]).unwrap();
            let handle = signals.handle();

            let mut guard = SIGHDL.lock();
            *guard = Some(handle);

            let th = thread::spawn(move || handler(signals));
            *THREAD.lock() = Some(th);
        },
        (),
    );
}

#[cfg(target_os = "windows")]
pub(crate) fn init() {
    INITIALIZER.init(
        || {
            let term = Arc::clone(&IS_HALT);
            signal_hook::flag::register(SIGTERM | SIGINT, Arc::clone(&term)).unwrap();
            let th = thread::spawn(move || handler(term));
            *THREAD.lock() = Some(th);
        },
        (),
    );
}

pub(crate) fn register_guard_condition(cond: GuardCondition) {
    let mut guard = get_guard_condition();
    guard.insert(KeyCond(cond.cond.as_ptr()), cond);
}

pub(crate) fn unregister_guard_condition(cond: &GuardCondition) {
    let mut guard = get_guard_condition();
    guard.remove(&KeyCond(cond.cond.as_ptr()));
}

/// After receiving SIGINT, SIGTERM, SIGQUIT, or SIGHUP, this function return `true`.
/// If `is_halt()` is `true`, some functions to receive or wait returns error to halt the process.
pub fn is_halt() -> bool {
    IS_HALT.load(Ordering::Relaxed)
}

#[cfg(not(target_os = "windows"))]
pub(crate) fn halt() {
    let mut sig = SIGHDL.lock();
    let sig = if let Some(sig) = std::mem::replace(&mut *sig, None) {
        sig
    } else {
        return;
    };
    sig.close();

    let mut th = THREAD.lock();
    let th = if let Some(th) = std::mem::replace(&mut *th, None) {
        th
    } else {
        return;
    };
    th.join().unwrap();
}
#[cfg(target_os = "windows")]
pub(crate) fn halt() {}

fn get_guard_condition() -> MutexGuard<'static, RawMutex, ConditionSet> {
    init();
    GUARD_COND.lock()
}

#[cfg(not(target_os = "windows"))]
fn handler(mut signals: SignalsInfo) {
    for signal in signals.forever() {
        match signal {
            SIGTERM | SIGINT | SIGQUIT | SIGHUP => {
                IS_HALT.store(true, Ordering::SeqCst);
                let mut cond = get_guard_condition();
                let cond = std::mem::take(&mut *cond);

                for (_, c) in cond {
                    c.trigger().unwrap();
                }

                let logger = Logger::new("safe_drive");
                pr_info_in!(logger, "Received signal: {signal}");
                break;
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(target_os = "windows")]
fn handler(term: Arc<AtomicBool>) {
    while !term.load(Ordering::Relaxed) {}
    let logger = Logger::new("safe_drive");
    pr_info_in!(logger, "Received signal");
}
