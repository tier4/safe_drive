use crate::{
    helper::InitOnce,
    logger::{pr_info_in, Logger},
    rcl,
    selector::guard_condition::GuardCondition,
};
use once_cell::sync::Lazy;
use parking_lot::{lock_api::MutexGuard, Mutex, RawMutex};
use signal_hook::{
    consts::*,
    iterator::{Handle, Signals, SignalsInfo},
};
use std::{
    collections::BTreeMap,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    thread::{self, JoinHandle},
};

#[derive(Eq, PartialEq, Ord, PartialOrd)]
struct KeyCond(*const rcl::rcl_guard_condition_t);

unsafe impl Sync for KeyCond {}
unsafe impl Send for KeyCond {}

type ConditionSet = BTreeMap<KeyCond, Arc<GuardCondition>>;

static INITIALIZER: InitOnce = InitOnce::new();
static GUARD_COND: Lazy<Mutex<ConditionSet>> = Lazy::new(|| Mutex::new(ConditionSet::new()));
static SIGHDL: Lazy<Mutex<Option<Handle>>> = Lazy::new(|| Mutex::new(None));
static THREAD: Lazy<Mutex<Option<JoinHandle<()>>>> = Lazy::new(|| Mutex::new(None));
static IS_HALT: AtomicBool = AtomicBool::new(false);

fn init() {
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

pub(crate) fn register_guard_condition(cond: Arc<GuardCondition>) {
    let mut guard = get_guard_condition();
    guard.insert(KeyCond(cond.cond.as_ptr()), cond);
}

pub(crate) fn unregister_guard_condition(cond: &GuardCondition) {
    let mut guard = get_guard_condition();
    guard.remove(&KeyCond(cond.cond.as_ptr()));
}

pub fn is_halt() -> bool {
    IS_HALT.load(Ordering::Relaxed)
}

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

fn get_guard_condition() -> MutexGuard<'static, RawMutex, ConditionSet> {
    init();
    GUARD_COND.lock()
}

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
