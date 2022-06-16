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
            if !self.lock.load(Ordering::Relaxed) {
                if self
                    .lock
                    .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
                {
                    let result = f();
                    self.is_init.store(true, Ordering::Release);
                    return result;
                }
            }
        }

        default
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
