use crate::{context::Context, error::RCLResult, rcl};
use std::sync::Arc;

pub(crate) struct RCLGuardCondition {
    pub(crate) cond: Box<rcl::rcl_guard_condition_t>,
    _context: Arc<Context>,
}

impl RCLGuardCondition {
    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_guard_condition_t {
        self.cond.as_ref() as *const _
    }

    pub(crate) unsafe fn as_ptr_mut(&self) -> *mut rcl::rcl_guard_condition_t {
        self.cond.as_ref() as *const _ as *mut _
    }
}

impl Drop for RCLGuardCondition {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_guard_condition_fini(self.cond.as_mut()).unwrap();
    }
}

#[derive(Clone)]
pub(crate) struct GuardCondition {
    pub(crate) cond: Arc<RCLGuardCondition>,
}

impl GuardCondition {
    pub(crate) fn new(context: Arc<Context>) -> RCLResult<Self> {
        let mut guard_condition = rcl::MTSafeFn::rcl_get_zero_initialized_guard_condition();
        let allocator = rcl::MTSafeFn::rcutils_get_default_allocator();

        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_guard_condition_init(
                &mut guard_condition,
                unsafe { context.as_ptr_mut() },
                rcl::rcl_guard_condition_options_t { allocator },
            )?;
        }

        let cond = Arc::new(RCLGuardCondition {
            cond: Box::new(guard_condition),
            _context: context,
        });
        Ok(GuardCondition { cond })
    }

    pub(crate) fn trigger(&self) -> RCLResult<()> {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_trigger_guard_condition(unsafe { self.cond.as_ptr_mut() })
    }
}

unsafe impl Sync for GuardCondition {}
unsafe impl Send for GuardCondition {}
