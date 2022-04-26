use crate::rcl;
use std::time::Duration;

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
