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

struct ConditionHandler<T> {
    event: T,
    handler: Box<dyn Fn()>,
}

pub struct Selector {
    wait_set: rcl::rcl_wait_set_t,
    subscriptions: BTreeMap<*const rcl::rcl_subscription_t, ConditionHandler<Arc<RCLSubscription>>>,
    cond: BTreeMap<*const rcl::rcl_guard_condition_t, ConditionHandler<Arc<RCLGuardCondition>>>,
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
            subscriptions: Default::default(),
            cond: Default::default(),
            _context: context,
        })
    }

    pub fn add_subscriber<T>(&mut self, subscriber: &Subscriber<T>, handler: Box<dyn Fn()>) {
        self.subscriptions.insert(
            subscriber.subscription.subscription.as_ref(),
            ConditionHandler {
                event: subscriber.subscription.clone(),
                handler,
            },
        );
    }

    fn add_guard_condition(&mut self, cond: &GuardCondition, handler: Box<dyn Fn()>) {
        self.cond.insert(
            cond.cond.cond.as_ref(),
            ConditionHandler {
                event: cond.cond.clone(),
                handler,
            },
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
                self.cond.len() as rcl::size_t,
                0,
                0,
                0,
                0,
            )?;

            // set subscriptions
            for (_, h) in self.subscriptions.iter() {
                guard.rcl_wait_set_add_subscription(
                    &mut self.wait_set,
                    h.event.subscription.as_ref(),
                    null_mut(),
                )?;
            }

            // set guard conditions
            for (_, h) in self.cond.iter() {
                guard.rcl_wait_set_add_guard_condition(
                    &mut self.wait_set,
                    h.event.cond.as_ref(),
                    null_mut(),
                )?;
            }
        }

        if let Some(t) = timeout {
            rcl::MTSafeFn::rcl_wait(&mut self.wait_set, t.as_secs() as i64);
        } else {
            rcl::MTSafeFn::rcl_wait(&mut self.wait_set, -1); // wait forever until arriving events
        }

        // notify subscritions
        for i in 0..self.subscriptions.len() {
            unsafe {
                let p = self.wait_set.subscriptions.offset(i as isize);
                if *p != null() {
                    debug_assert!(self.subscriptions.contains_key(&*p));
                    if let Some(h) = self.subscriptions.get(&*p) {
                        (h.handler)();
                    }
                }
            }
        }

        // notify guard conditions
        for i in 0..self.cond.len() {
            unsafe {
                let p = self.wait_set.guard_conditions.offset(i as isize);
                if *p != null() {
                    debug_assert!(self.cond.contains_key(&*p));
                    if let Some(h) = self.cond.get(&*p) {
                        (h.handler)();
                    }
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

struct RCLGuardCondition {
    cond: Box<rcl::rcl_guard_condition_t>,
    _context: Arc<Context>,
}

impl RCLGuardCondition {
    unsafe fn as_ptr_mut(&self) -> *mut rcl::rcl_guard_condition_t {
        self.cond.as_ref() as *const _ as *mut _
    }
}

impl Drop for RCLGuardCondition {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
        guard.rcl_guard_condition_fini(self.cond.as_mut()).unwrap();
    }
}

struct GuardCondition {
    cond: Arc<RCLGuardCondition>,
}

impl GuardCondition {
    fn new(context: Arc<Context>) -> RCLResult<Arc<Self>> {
        let mut guard_condition = rcl::MTSafeFn::rcl_get_zero_initialized_guard_condition();
        let allocator = rcl::MTSafeFn::rcutils_get_default_allocator();

        {
            let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
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
        Ok(Arc::new(GuardCondition { cond: cond }))
    }

    fn trigger(&self) -> RCLResult<()> {
        let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
        guard.rcl_trigger_guard_condition(unsafe { self.cond.as_ptr_mut() })
    }
}

unsafe impl Sync for GuardCondition {}
unsafe impl Send for GuardCondition {}

#[cfg(test)]
mod test {
    use std::thread;

    use crate::{context::Context, error::RCLResult};

    #[test]
    fn test_guard_condition() -> RCLResult<()> {
        let ctx = Context::new()?;
        let cond = super::GuardCondition::new(ctx.clone())?;

        let ctx2 = ctx.clone();
        let cond2 = cond.clone();

        let w = thread::spawn(move || {
            let mut selector = super::Selector::new(ctx2).unwrap();
            selector.add_guard_condition(&cond2, Box::new(|| println!("triggerd!")));
            selector.wait(None).unwrap();
        });

        cond.trigger()?;
        w.join().unwrap();

        Ok(())
    }
}
