use crate::{
    context::Context,
    error::RCLResult,
    rcl,
    subscriber::{RCLSubscription, Subscriber},
};
use std::{
    collections::BTreeMap,
    ptr::{null, null_mut},
    sync::Arc,
    time::Duration,
};

pub struct Selector {
    wait_set: rcl::rcl_wait_set_t,
    subscriptions: BTreeMap<*const rcl::rcl_subscription_t, Arc<RCLSubscription>>,
    _context: Arc<Context>,
}

impl Selector {
    pub fn new(context: Arc<Context>) -> RCLResult<Self> {
        let mut wait_set = rcl::MTSafeFn::rcl_get_zero_initialized_wait_set();

        {
            let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
            guard.rcl_wait_set_init(
                &mut wait_set,
                0,
                0,
                0,
                0,
                0,
                0,
                unsafe { context.as_ptr_mut() },
                rcl::MTSafeFn::rcutils_get_default_allocator(),
            )?;
        }

        Ok(Selector {
            wait_set,
            subscriptions: BTreeMap::new(),
            _context: context,
        })
    }

    pub fn add_subscriber<T>(&mut self, subscriber: &Subscriber<T>) {
        self.subscriptions.insert(
            subscriber.subscription.subscription.as_ref(),
            subscriber.subscription.clone(),
        );
    }

    pub fn remove_subscriber<T>(&mut self, subscriber: &Subscriber<T>) {
        self.subscriptions
            .remove(&(subscriber.subscription.subscription.as_ref() as *const _));
    }

    pub fn wait(&mut self, timeout: Option<Duration>) -> RCLResult<()> {
        {
            let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
            guard.rcl_wait_set_clear(&mut self.wait_set)?;
            guard.rcl_wait_set_resize(
                &mut self.wait_set,
                self.subscriptions.len() as rcl::size_t,
                0,
                0,
                0,
                0,
                0,
            )?;

            for (_, s) in self.subscriptions.iter() {
                guard.rcl_wait_set_add_subscription(
                    &mut self.wait_set,
                    s.subscription.as_ref(),
                    null_mut(),
                )?;
            }
        }

        if let Some(t) = timeout {
            rcl::MTSafeFn::rcl_wait(&mut self.wait_set, t.as_secs() as i64);
        } else {
            rcl::MTSafeFn::rcl_wait(&mut self.wait_set, -1); // wait forever until arriving events
        }

        for i in 0..self.subscriptions.len() {
            unsafe {
                let p = self.wait_set.subscriptions.offset(i as isize);
                if *p != null() {
                    debug_assert!(self.subscriptions.contains_key(&*p));
                }
            }
        }

        Ok(())
    }
}

impl Drop for Selector {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
        guard.rcl_wait_set_fini(&mut self.wait_set).unwrap()
    }
}
