use std::mem::MaybeUninit;

use crate::{error::RCLResult, get_allocator, rcl};

/// A clock. For now only SystemTime/ROSTime is implemented.
pub struct Clock {
    clock: rcl::rcl_clock_t,
}

impl Clock {
    /// Create a clock.
    pub fn new() -> RCLResult<Self> {
        let mut clock: rcl::rcl_clock_t = unsafe { MaybeUninit::zeroed().assume_init() };

        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_ros_clock_init(&mut clock, &mut get_allocator())?;

        Ok(Self { clock })
    }

    pub(crate) fn as_ptr_mut(&self) -> *mut rcl::rcl_clock_t {
        &self.clock as *const _ as *mut _
    }

    pub fn get_now(&mut self) -> RCLResult<rcl::rcl_time_point_value_t> {
        let mut now = unsafe { MaybeUninit::zeroed().assume_init() };
        rcl::MTSafeFn::rcl_clock_get_now(&mut self.clock, &mut now)?;
        Ok(now)
    }
}

impl Drop for Clock {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_ros_clock_fini(&mut self.clock);
    }
}
