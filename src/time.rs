//! Translator between ROS2's time types and Rust's `SystemTime`.

use crate::{
    logger::{pr_fatal_in, Logger},
    msg::builtin_interfaces,
    rcl,
};
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

impl From<&SystemTime> for builtin_interfaces::UnsafeTime {
    fn from(t: &SystemTime) -> Self {
        let dur = t.duration_since(SystemTime::UNIX_EPOCH).unwrap();

        let sec = dur.as_secs();
        if sec > i32::MAX as u64 {
            let logger = Logger::new("safe_drive");
            pr_fatal_in!(logger, "Encountered the year-2038 problem.");
            panic!("Year-2038 problem.");
        }

        builtin_interfaces::UnsafeTime {
            sec: sec as i32,
            nanosec: dur.subsec_nanos(),
        }
    }
}

impl From<SystemTime> for builtin_interfaces::UnsafeTime {
    fn from(t: SystemTime) -> Self {
        (&t).into()
    }
}

impl From<&builtin_interfaces::UnsafeTime> for SystemTime {
    fn from(t: &builtin_interfaces::UnsafeTime) -> Self {
        let nanos = Duration::from_nanos(t.nanosec as u64);
        let secs = Duration::from_secs(t.sec as u64);
        let dur = nanos + secs;
        SystemTime::UNIX_EPOCH + dur
    }
}

impl From<builtin_interfaces::UnsafeTime> for SystemTime {
    fn from(t: builtin_interfaces::UnsafeTime) -> Self {
        (&t).into()
    }
}

impl From<&Duration> for builtin_interfaces::UnsafeDuration {
    fn from(t: &Duration) -> Self {
        let sec = t.as_secs();

        if sec > i32::MAX as u64 {
            let logger = Logger::new("safe_drive");
            pr_fatal_in!(logger, "Encountered the year-2038 problem.");
            panic!("Year-2038 problem.");
        }

        let nanosec = t.subsec_nanos();

        builtin_interfaces::UnsafeDuration {
            sec: sec as i32,
            nanosec,
        }
    }
}

impl From<Duration> for builtin_interfaces::UnsafeDuration {
    fn from(t: Duration) -> Self {
        (&t).into()
    }
}

impl From<&builtin_interfaces::UnsafeDuration> for Duration {
    fn from(t: &builtin_interfaces::UnsafeDuration) -> Self {
        assert!(t.sec > 0);
        Duration::new(t.sec as u64, t.nanosec)
    }
}

impl From<builtin_interfaces::UnsafeDuration> for Duration {
    fn from(t: builtin_interfaces::UnsafeDuration) -> Self {
        (&t).into()
    }
}

pub(crate) fn rcl_time_to_system_time(t: rcl::rcutils_time_point_value_t) -> SystemTime {
    let from_epoch = Duration::from_nanos(t as u64);
    SystemTime::UNIX_EPOCH + from_epoch
}
