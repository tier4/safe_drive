# Initialize Once

`struct InitOnce` provides a mechanisms for an initialization,
and it is performed just once.
[init_once.tla](./init_once.tla) is the specification of the initializer.

## Variables

There are 3 global variables.

```tla+
lock = FALSE;
is_init = FALSE;

pids = {};
```

`lock` and `is_init` are used by the algorithm.
`pids` is a set of process IDs which perform the initialization.

## What do we check?

- Deadlock freedom
- Termination
- Initialization is performed just once

The just once property can be tested as follows.

```tla+
just_one == Cardinality(pids) <= 1
```

## The initializer in Rust

The initializer is in [helper.rs](../../src/helper.rs).

```rust
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
```
