use crate::rcl;
use std::time::{Duration, SystemTime};

impl From<rcl::rmw_time_t> for Duration {
    fn from(t: rcl::rmw_time_t) -> Self {
        Duration::new(t.sec, t.nsec as u32)
    }
}

impl From<Duration> for rcl::rmw_time_t {
    fn from(t: Duration) -> Self {
        rcl::rmw_time_t {
            sec: t.as_secs(),
            nsec: t.subsec_nanos() as _,
        }
    }
}

pub(crate) fn rcl_time_to_system_time(t: rcl::rcutils_time_point_value_t) -> SystemTime {
    let from_epoch = Duration::from_nanos(t as u64);
    SystemTime::UNIX_EPOCH + from_epoch
}
