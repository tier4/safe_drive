use std::sync::atomic::{AtomicBool, Ordering};

pub struct InitOnce {
    lock: AtomicBool,
    is_init: AtomicBool,
}

impl InitOnce {
    pub const fn new() -> Self {
        InitOnce {
            lock: AtomicBool::new(false),
            is_init: AtomicBool::new(false),
        }
    }

    pub fn init<F, R>(&self, f: F, default: R) -> R
    where
        F: Fn() -> R,
    {
        while !self.is_init.load(Ordering::Relaxed) {
            if !self.lock.load(Ordering::Relaxed)
                && self
                    .lock
                    .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
            {
                let result = f();
                self.is_init.store(true, Ordering::Release);
                return result;
            }
        }

        default
    }
}

#[cfg(feature = "statistics")]
pub mod statistics {
    use serde::Serialize;
    use std::time::Duration;

    #[derive(Serialize, Debug)]
    pub struct SerializableTimeStat {
        pub min: Option<Duration>,
        pub max: Option<Duration>,
        pub data: Vec<f64>,
    }

    #[derive(Debug)]
    pub struct TimeStatistics<const N: usize> {
        min: Option<Duration>,
        max: Option<Duration>,
        data: Box<[Option<Duration>; N]>,
        idx: usize,
        mask: usize,
    }

    impl<const N: usize> TimeStatistics<N> {
        pub fn new() -> Self {
            assert_ne!(N, 0);

            // N must be 2^m where m >= 0.
            let mask = (1 << ((0_usize).leading_zeros() - N.leading_zeros() - 1)) - 1;
            assert_eq!(N & mask, 0);

            Self {
                min: None,
                max: None,
                data: Box::new([None; N]),
                idx: 0,
                mask,
            }
        }

        pub fn add(&mut self, dur: Duration) {
            if let Some(min) = self.min {
                if dur < min {
                    self.min = Some(dur);
                }
            } else {
                self.min = Some(dur);
            }

            if let Some(max) = self.max {
                if dur > max {
                    self.max = Some(dur);
                }
            } else {
                self.max = Some(dur);
            }

            self.data[self.idx] = Some(dur);
            self.idx += 1;
            self.idx &= self.mask;
        }

        pub fn to_serializable(&self) -> SerializableTimeStat {
            let mut data = Vec::new();
            for dur in self.data.iter().flatten() {
                data.push(dur.as_secs_f64());
            }

            SerializableTimeStat {
                min: self.min,
                max: self.max,
                data,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::helper::InitOnce;

    static INITIALIZER: InitOnce = InitOnce::new();
    static mut N: usize = 0;

    #[test]
    fn test_init_once() {
        fn init_n() {
            unsafe {
                N += 1;
            }
        }

        let th = std::thread::spawn(|| INITIALIZER.init(init_n, ()));
        INITIALIZER.init(init_n, ());
        INITIALIZER.init(init_n, ());
        INITIALIZER.init(init_n, ());
        th.join().unwrap();

        assert_eq!(unsafe { N }, 1);
    }
}
