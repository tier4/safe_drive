use self::guard_condition::{GuardCondition, RCLGuardCondition};
use crate::{
    context::Context,
    error::{RCLError, RCLResult},
    rcl,
    service::{
        client::{ClientData, ClientRecv},
        server::{Server, ServerData},
    },
    topic::subscriber::{RCLSubscription, Subscriber},
};
use std::{collections::BTreeMap, ptr::null_mut, sync::Arc, time::Duration};

pub(crate) mod async_selector;
mod guard_condition;

struct ConditionHandler<T> {
    is_once: bool,
    event: T,
    handler: Option<Box<dyn Fn()>>,
}

pub struct Selector {
    wait_set: rcl::rcl_wait_set_t,
    services: BTreeMap<*const rcl::rcl_service_t, ConditionHandler<Arc<ServerData>>>,
    clients: BTreeMap<*const rcl::rcl_client_t, ConditionHandler<Arc<ClientData>>>,
    subscriptions: BTreeMap<*const rcl::rcl_subscription_t, ConditionHandler<Arc<RCLSubscription>>>,
    cond: BTreeMap<*const rcl::rcl_guard_condition_t, ConditionHandler<Arc<RCLGuardCondition>>>,
    context: Arc<Context>,
}

impl Selector {
    pub(crate) fn new(context: Arc<Context>) -> RCLResult<Self> {
        let mut wait_set = rcl::MTSafeFn::rcl_get_zero_initialized_wait_set();

        {
            let guard = rcl::MT_UNSAFE_FN.lock();
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
            services: Default::default(),
            clients: Default::default(),
            cond: Default::default(),
            context,
        })
    }

    pub fn add_subscriber<T>(
        &mut self,
        subscriber: &Subscriber<T>,
        handler: Option<Box<dyn Fn()>>,
        is_once: bool,
    ) -> bool {
        if self.context.as_ptr() == subscriber.subscription.node.context.as_ptr() {
            self.add_rcl_subscription(subscriber.subscription.clone(), handler, is_once);
            true
        } else {
            false
        }
    }

    pub(crate) fn add_rcl_subscription(
        &mut self,
        subscription: Arc<RCLSubscription>,
        handler: Option<Box<dyn Fn()>>,
        is_once: bool,
    ) {
        self.subscriptions.insert(
            subscription.subscription.as_ref(),
            ConditionHandler {
                event: subscription,
                handler,
                is_once,
            },
        );
    }

    pub fn add_server<T1, T2>(
        &mut self,
        server: &Server<T1, T2>,
        handler: Option<Box<dyn Fn()>>,
        is_once: bool,
    ) -> bool {
        if self.context.as_ptr() == server.data.node.context.as_ptr() {
            self.add_server_data(server.data.clone(), handler, is_once);
            true
        } else {
            false
        }
    }

    pub(crate) fn add_server_data(
        &mut self,
        server: Arc<ServerData>,
        handler: Option<Box<dyn Fn()>>,
        is_once: bool,
    ) {
        if self.context.as_ptr() == server.node.context.as_ptr() {
            self.services.insert(
                &server.service,
                ConditionHandler {
                    event: server,
                    handler,
                    is_once,
                },
            );
        }
    }

    pub fn add_client<T1, T2>(
        &mut self,
        client: &ClientRecv<T1, T2>,
        handler: Option<Box<dyn Fn()>>,
        is_once: bool,
    ) -> bool {
        if self.context.as_ptr() == client.data.node.context.as_ptr() {
            self.add_client_data(client.data.clone(), handler, is_once);
            true
        } else {
            false
        }
    }

    pub(crate) fn add_client_data(
        &mut self,
        client: Arc<ClientData>,
        handler: Option<Box<dyn Fn()>>,
        is_once: bool,
    ) {
        self.clients.insert(
            &client.client,
            ConditionHandler {
                event: client,
                handler,
                is_once,
            },
        );
    }

    fn add_guard_condition(&mut self, cond: &GuardCondition, handler: Option<Box<dyn Fn()>>) {
        self.cond.insert(
            cond.cond.cond.as_ref(),
            ConditionHandler {
                event: cond.cond.clone(),
                handler,
                is_once: false,
            },
        );
    }

    pub fn remove_subscriber<T>(&mut self, subscriber: &Subscriber<T>) {
        self.subscriptions
            .remove(&(subscriber.subscription.subscription.as_ref() as *const _));
    }

    pub(crate) fn remove_rcl_subscription(&mut self, subscription: &Arc<RCLSubscription>) {
        self.subscriptions
            .remove(&(subscription.subscription.as_ref() as *const _));
    }

    pub(crate) fn remove_server_data(&mut self, server: &Arc<ServerData>) {
        self.services.remove(&(&server.service as *const _));
    }

    pub(crate) fn remove_client_data(&mut self, client: &Arc<ClientData>) {
        self.clients.remove(&(&client.client as *const _));
    }

    pub fn wait(&mut self, timeout: Option<Duration>) -> RCLResult<()> {
        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_wait_set_clear(&mut self.wait_set)?;
            guard.rcl_wait_set_resize(
                &mut self.wait_set,
                self.subscriptions.len() as rcl::size_t,
                self.cond.len() as rcl::size_t,
                0,
                self.clients.len() as rcl::size_t,
                self.services.len() as rcl::size_t,
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

            // set clients
            for (_, h) in self.clients.iter() {
                guard.rcl_wait_set_add_client(&mut self.wait_set, &h.event.client, null_mut())?;
            }

            // set services
            for (_, h) in self.services.iter() {
                guard.rcl_wait_set_add_service(&mut self.wait_set, &h.event.service, null_mut())?;
            }
        }

        if let Some(t) = timeout {
            match rcl::MTSafeFn::rcl_wait(&mut self.wait_set, t.as_secs() as i64) {
                Ok(_) | Err(RCLError::Timeout) => (),
                Err(e) => return Err(e),
            }
        } else {
            // wait forever until arriving events
            rcl::MTSafeFn::rcl_wait(&mut self.wait_set, -1)?;
        }

        // notify subscriptions
        notify(&mut self.subscriptions, self.wait_set.subscriptions);

        // notify services
        notify(&mut self.services, self.wait_set.services);

        // notify clients
        notify(&mut self.clients, self.wait_set.clients);

        // notify guard conditions
        notify(&mut self.cond, self.wait_set.guard_conditions);

        Ok(())
    }
}

impl Drop for Selector {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_wait_set_fini(&mut self.wait_set).unwrap()
    }
}

fn notify<K, V>(m: &mut BTreeMap<*const K, ConditionHandler<V>>, array: *const *const K) {
    for i in 0..m.len() {
        unsafe {
            let p = *array.add(i);
            if !p.is_null() {
                debug_assert!(m.contains_key(&p));
                if let Some(h) = m.get(&p) {
                    if let Some(hdl) = &h.handler {
                        hdl()
                    }
                    if h.is_once {
                        m.remove(&p);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{context::Context, error::RCLResult};
    use std::thread;

    #[test]
    fn test_guard_condition() -> RCLResult<()> {
        let ctx = Context::new()?;
        let cond = super::GuardCondition::new(ctx.clone())?;

        let ctx2 = ctx.clone();
        let cond2 = cond.clone();

        let w = thread::spawn(move || {
            let mut selector = super::Selector::new(ctx2).unwrap();
            selector.add_guard_condition(&cond2, Some(Box::new(|| println!("triggerd!"))));
            selector.wait(None).unwrap();
        });

        cond.trigger()?;
        w.join().unwrap();

        Ok(())
    }
}
