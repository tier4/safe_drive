//! Selector provides functions like `select` or `epoll`.
//! This is used to single threaded execution.
//! For multi threaded execution, this is used internally.
//!
//! # Example
//!
//! ```
//! use safe_drive::{
//!     context::Context, logger::Logger, msg::common_interfaces::std_msgs, pr_info,
//! };
//! use std::time::Duration;
//!
//! // First of all, you need create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create a subscribe node.
//! let node_sub = ctx
//!     .create_node("selector_rs", None, Default::default())
//!     .unwrap();
//!
//! // Create a subscriber.
//! let subscriber = node_sub
//!     .create_subscriber::<std_msgs::msg::String>("selector_topic", None)
//!     .unwrap();
//!
//! // Create a selector, which is for IO multiplexing.
//! let mut selector = ctx.create_selector().unwrap();
//!
//! // Create a logger.
//! let logger_sub = Logger::new("selector_rs");
//!
//! // Add subscriber to the selector.
//! // The 2nd argument is a callback function.
//! // If data arrive, the callback will be invoked.
//! // The 3rd argument is used to specify the callback will be invoked only once or infinitely.
//! // If the 3rd argument is `true`, the callback function is invoked once and unregistered.
//! selector.add_subscriber(
//!     subscriber,
//!     Box::new(move |msg| {
//!         // Print the message
//!         pr_info!(logger_sub, "Received: msg = {}", msg.data); // Print a message.
//!     }),
//!     false,
//! );
//!
//! // Create a wall timer, which invoke the callback periodically.
//! selector.add_wall_timer(
//!     "timer_name", // name of the timer
//!     Duration::from_millis(100),
//!     Box::new(move || ()),
//! );
//!
//! // Spin.
//! for _ in 0..10 {
//!     selector.wait().unwrap();
//! }
//! ```

use self::guard_condition::{GuardCondition, RCLGuardCondition};
use crate::{
    context::Context,
    delta_list::DeltaList,
    error::{DynError, RCLError, RCLResult},
    logger::{pr_error_in, Logger},
    msg::{ServiceMsg, TopicMsg},
    rcl,
    service::{
        client::{ClientData, ClientRecv},
        server::{Server, ServerData},
        Header,
    },
    signal_handler,
    topic::subscriber::{RCLSubscription, Subscriber},
    PhantomUnsend, PhantomUnsync, RecvResult, ST,
};
use std::{
    collections::BTreeMap,
    mem::replace,
    ptr::null_mut,
    rc::Rc,
    sync::Arc,
    time::{Duration, SystemTime},
};

#[cfg(feature = "statistics")]
use serde::Serialize;

#[cfg(feature = "statistics")]
use crate::helper::statistics::{SerializableTimeStat, TimeStatistics};

pub(crate) mod async_selector;
pub(crate) mod guard_condition;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum CallbackResult {
    Ok,
    Remove,
}

struct ConditionHandler<T> {
    is_once: bool,
    event: T,
    handler: Option<Box<dyn FnMut() -> CallbackResult>>,
}

enum TimerType {
    WallTimer(Rc<String>, Duration),
    OneShot,
}

#[cfg(feature = "statistics")]
#[derive(Debug)]
struct TimeStat {
    #[cfg(feature = "rcl_stat")]
    rcl_wait: TimeStatistics<4096>,

    callback: BTreeMap<*const (), (String, TimeStatistics<4096>)>,
    wall_timer: BTreeMap<String, TimeStatistics<4096>>,
}

#[cfg(feature = "statistics")]
#[derive(Serialize, Debug)]
pub struct Statistics {
    #[cfg(feature = "rcl_stat")]
    pub rcl_wait: SerializableTimeStat,

    #[cfg(feature = "rcl_stat")]
    pub rcl_take: Vec<SerializableTimeStat>,

    pub callback: BTreeMap<String, SerializableTimeStat>, // callback functions of subscribers and servers
    pub wall_timer: BTreeMap<String, SerializableTimeStat>, // wall timers
}

/// Selector invokes callback functions associated with subscribers, services, timers, or condition variables.
/// Selector cannot send to another thread and shared by multiple threads.
/// So, use this for single threaded execution.
///
/// # Example
///
/// ```
/// use safe_drive::context::Context;
///
/// let ctx = Context::new().unwrap();
/// let mut selector = ctx.create_selector(); // Create a new selector.
/// ```
pub struct Selector {
    timer: DeltaList<ConditionHandler<TimerType>>,
    base_time: SystemTime,
    signal_cond: Arc<GuardCondition>,
    wait_set: rcl::rcl_wait_set_t,
    services: BTreeMap<*const rcl::rcl_service_t, ConditionHandler<Arc<ServerData>>>,
    clients: BTreeMap<*const rcl::rcl_client_t, ConditionHandler<Arc<ClientData>>>,
    subscriptions: BTreeMap<*const rcl::rcl_subscription_t, ConditionHandler<Arc<RCLSubscription>>>,
    cond: BTreeMap<*const rcl::rcl_guard_condition_t, ConditionHandler<Arc<RCLGuardCondition>>>,
    context: Arc<Context>,

    #[cfg(feature = "statistics")]
    time_stat: TimeStat,

    _unused: (PhantomUnsync, PhantomUnsend),
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

        #[cfg(feature = "statistics")]
        let time_stat = TimeStat {
            #[cfg(feature = "rcl_stat")]
            rcl_wait: TimeStatistics::new(),

            callback: BTreeMap::new(),
            wall_timer: BTreeMap::new(),
        };

        let signal_cond = GuardCondition::new(context.clone())?;
        let mut selector = Selector {
            timer: DeltaList::Nil,
            base_time: SystemTime::now(),
            signal_cond: signal_cond.clone(),
            wait_set,
            subscriptions: Default::default(),
            services: Default::default(),
            clients: Default::default(),
            cond: Default::default(),
            context,

            #[cfg(feature = "statistics")]
            time_stat,

            _unused: (Default::default(), Default::default()),
        };

        selector.add_guard_condition(signal_cond.as_ref(), None);
        signal_handler::register_guard_condition(signal_cond);

        Ok(selector)
    }

    #[cfg(feature = "statistics")]
    pub fn statistics(&self) -> Statistics {
        let callback = self
            .time_stat
            .callback
            .iter()
            .map(|(_, (k, v))| (k.clone(), v.to_serializable()))
            .collect();

        let wall_timer = self
            .time_stat
            .wall_timer
            .iter()
            .map(|(k, v)| (k.clone(), v.to_serializable()))
            .collect();

        #[cfg(feature = "rcl_stat")]
        let mut rcl_take = Vec::new();

        #[cfg(feature = "rcl_stat")]
        for (_, v) in self.subscriptions.iter() {
            let guard = v.event.latency_take.lock();
            let s = guard.to_serializable();
            rcl_take.push(s);
        }

        Statistics {
            #[cfg(feature = "rcl_stat")]
            rcl_wait: self.time_stat.rcl_wait.to_serializable(),

            #[cfg(feature = "rcl_stat")]
            rcl_take,

            callback,
            wall_timer,
        }
    }

    /// Register a subscriber with callback function.
    /// The callback function will be invoked when arriving data.
    ///
    /// # Error
    ///
    /// If a selector takes a subscriber created by a different context,
    /// `add_subscriber()` must fail.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::common_interfaces::std_msgs, node::Node, selector::Selector};
    /// use std::sync::Arc;
    ///
    /// fn add_new_subscriber(selector: &mut Selector, node: Arc<Node>) {
    ///     // Create a subscriber.
    ///     let subscriber = node.create_subscriber("node_name", None).unwrap();
    ///
    ///     // Add the subscriber with a callback function.
    ///     selector.add_subscriber(
    ///         subscriber,
    ///         Box::new(|msg: std_msgs::msg::Bool| /* some tasks */ ()), // Callback function.
    ///         true,
    ///     );
    /// }
    /// ```
    pub fn add_subscriber<T: TopicMsg + 'static>(
        &mut self,
        subscriber: Subscriber<T>,
        mut handler: Box<dyn FnMut(T)>,
        is_once: bool,
    ) -> bool {
        let sub = subscriber.subscription.clone();
        let context_ptr = subscriber.subscription.node.context.as_ptr();

        #[cfg(feature = "statistics")]
        let symbol = {
            let node_name = subscriber.subscription.node.get_name();
            let node_namespace =
                if let Some(namespace) = subscriber.subscription.node.get_namespace() {
                    namespace.as_str()
                } else {
                    ""
                };
            let topic_name = subscriber.get_topic_name();
            format!("{node_namespace}:{node_name}:subscriber:{topic_name}")
        };

        let f = move || {
            let start = SystemTime::now();
            let dur = Duration::from_millis(1);

            loop {
                match subscriber.try_recv() {
                    RecvResult::Ok(n) => {
                        handler(n);
                    }
                    RecvResult::RetryLater(()) => return CallbackResult::Ok,
                    RecvResult::Err(e) => {
                        let logger = Logger::new("safe_drive");
                        pr_error_in!(logger, "failed try_recv() of subscriber: {}", e);
                        return CallbackResult::Remove;
                    }
                }

                if let Ok(t) = start.elapsed() {
                    if t > dur {
                        return CallbackResult::Ok;
                    }
                } else {
                    return CallbackResult::Ok;
                }
            }
        };

        if self.context.as_ptr() == context_ptr {
            #[cfg(feature = "statistics")]
            {
                self.time_stat.callback.insert(
                    sub.subscription.as_ref() as *const _ as *const (),
                    (symbol, TimeStatistics::new()),
                );
            }

            self.add_rcl_subscription(sub, Some(Box::new(f)), is_once);
            true
        } else {
            false
        }
    }

    pub(crate) fn add_rcl_subscription(
        &mut self,
        subscription: Arc<RCLSubscription>,
        handler: Option<Box<dyn FnMut() -> CallbackResult>>,
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

    /// Register the subscriber with callback function.
    /// The callback function will be invoked when arriving data.
    ///
    /// The callback function must take `ServiceMsg::Request` and `Header` and
    /// return `ServiceMsg::Response`.
    ///
    /// # Error
    ///
    /// If a selector takes a server created by a different context,
    /// `add_server()` must fail.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{msg::{common_interfaces::std_srvs, ServiceMsg}, node::Node, selector::Selector};
    /// use std::sync::Arc;
    ///
    /// fn add_new_server(selector: &mut Selector, node: Arc<Node>) {
    ///     // Create a server.
    ///     let server = node
    ///         .create_server::<std_srvs::srv::Empty>("select_rs_service", None)
    ///         .unwrap();
    ///
    ///     // Add the server with a callback function.
    ///     selector.add_server(
    ///         server,
    ///         Box::new(|request: <std_srvs::srv::Empty as ServiceMsg>::Request, header| {
    ///             // Return the response.
    ///             let response = std_srvs::srv::EmptyResponse::new().unwrap();
    ///             response
    ///         }), // Callback function.
    ///         true,
    ///     );
    /// }
    /// ```
    pub fn add_server<T: ServiceMsg + 'static>(
        &mut self,
        server: Server<T>,
        mut handler: Box<dyn FnMut(T::Request, Header) -> T::Response>,
        is_once: bool,
    ) -> bool {
        let context_ptr = server.data.node.context.as_ptr();
        let srv = server.data.clone();
        let mut server = Some(server);

        let f = move || {
            let start = SystemTime::now();
            let dur = Duration::from_millis(1);

            loop {
                let s = server.take().unwrap();
                match s.try_recv_with_header() {
                    RecvResult::Ok((server_send, request, header)) => {
                        let result = handler(request, header);
                        match server_send.send(&result) {
                            Ok(s) => {
                                server = Some(s);
                            }
                            Err(e) => {
                                let logger = Logger::new("safe_drive");
                                pr_error_in!(logger, "{e}");
                                return CallbackResult::Remove;
                            }
                        }
                    }
                    RecvResult::RetryLater(srv) => {
                        server = Some(srv);
                        return CallbackResult::Ok;
                    }
                    RecvResult::Err(e) => {
                        let logger = Logger::new("safe_drive");
                        pr_error_in!(logger, "failed try_recv() of server: {}", e);
                        return CallbackResult::Remove;
                    }
                }

                if let Ok(t) = start.elapsed() {
                    if t > dur {
                        return CallbackResult::Ok;
                    }
                } else {
                    return CallbackResult::Ok;
                }
            }
        };

        if self.context.as_ptr() == context_ptr {
            self.add_server_data(srv, Some(Box::new(f)), is_once);
            true
        } else {
            false
        }
    }

    pub(crate) fn add_server_data(
        &mut self,
        server: Arc<ServerData>,
        handler: Option<Box<dyn FnMut() -> CallbackResult>>,
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

    /// Wait a response from a server.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     error::DynError, msg::common_interfaces::std_srvs, selector::Selector, service::client::Client,
    ///     RecvResult, ST,
    /// };
    ///
    /// fn worker(
    ///     mut selector: Selector,
    ///     mut sender: Client<std_srvs::srv::Empty>,
    /// ) -> Result<(), DynError> {
    ///     let msg = std_srvs::srv::EmptyRequest::new().unwrap();
    ///     loop {
    ///         // Send a request.
    ///         let receiver = sender.send(&msg)?;
    ///
    ///         // Make it single-threaded data.
    ///         let mut receiver = ST::new(receiver);
    ///
    ///         // Register the receiver to wait a response.
    ///         selector.add_client_recv(&receiver);
    ///
    ///         loop {
    ///             selector.wait()?; // Wait a response.
    ///
    ///             // Receive a message
    ///             match receiver.try_recv() {
    ///                 RecvResult::Ok((s, _response)) => {
    ///                     sender = s;
    ///                     break;
    ///                 }
    ///                 RecvResult::RetryLater(r) => {
    ///                     receiver = r;
    ///                 }
    ///                 RecvResult::Err(e) => return Err(e.into()),
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    pub fn add_client_recv<T>(&mut self, client: &ST<ClientRecv<T>>) {
        self.add_client_data(client.data.data.clone(), None, true);
    }

    pub(crate) fn add_client_data(
        &mut self,
        client: Arc<ClientData>,
        handler: Option<Box<dyn FnMut() -> CallbackResult>>,
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

    fn add_guard_condition(
        &mut self,
        cond: &GuardCondition,
        handler: Option<Box<dyn FnMut() -> CallbackResult>>,
    ) {
        self.cond.insert(
            cond.cond.cond.as_ref(),
            ConditionHandler {
                event: cond.cond.clone(),
                handler,
                is_once: false,
            },
        );
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

    /// Add a timer.
    /// The `handler` is called after `t` seconds later.
    /// The `handler` is called just once.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::selector::Selector;
    /// use std::time::Duration;
    ///
    /// fn add_new_timer(selector: &mut Selector) {
    ///     // Add a timer.
    ///     selector.add_timer(
    ///         Duration::from_millis(100),
    ///         Box::new(|| /* some tasks */ ()), // Callback function.
    ///     );
    /// }
    /// ```
    pub fn add_timer(&mut self, t: Duration, mut handler: Box<dyn FnMut()>) {
        self.add_timer_inner(
            t,
            Box::new(move || {
                handler();
                CallbackResult::Ok
            }),
            TimerType::OneShot,
        );
    }

    /// Add a wall timer.
    /// The `handler` is called after `t` seconds later.
    /// The `handler` will be automatically reloaded after calling it.
    /// It means the `handler` is called periodically.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::selector::Selector;
    /// use std::time::Duration;
    ///
    /// fn add_new_wall_timer(selector: &mut Selector) {
    ///     // Add a timer.
    ///     selector.add_wall_timer(
    ///         "tinmer_name",
    ///         Duration::from_millis(100),
    ///         Box::new(|| /* some tasks */ ()), // Callback function.
    ///     );
    /// }
    /// ```
    pub fn add_wall_timer(&mut self, name: &str, t: Duration, mut handler: Box<dyn FnMut()>) {
        #[cfg(feature = "statistics")]
        self.time_stat
            .wall_timer
            .insert(name.to_string(), TimeStatistics::new());

        self.add_timer_inner(
            t,
            Box::new(move || {
                handler();
                CallbackResult::Ok
            }),
            TimerType::WallTimer(Rc::new(name.to_string()), t),
        );
    }

    fn add_timer_inner(
        &mut self,
        t: Duration,
        handler: Box<dyn FnMut() -> CallbackResult>,
        timer_type: TimerType,
    ) {
        let now_time = SystemTime::now();

        if self.timer.is_empty() {
            self.base_time = now_time;
        }

        let delta = if let Ok(d) = now_time.duration_since(self.base_time) {
            // if base_time <= now_time
            // delta = now_time - base_time + t
            d + t
        } else {
            // if now_time < base_time
            // delta = t
            let d = self.base_time.duration_since(now_time).unwrap();

            if let Some(head) = self.timer.front_mut() {
                *head.0 += d; // update delta
            }
            self.base_time = now_time; // set base_time now
            t
        };

        self.timer.insert(
            delta,
            ConditionHandler {
                is_once: true,
                event: timer_type,
                handler: Some(handler),
            },
        );
    }

    /// Wait events and invoke registered callback functions.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{error::DynError, selector::Selector};
    ///
    /// fn wait_events(selector: &mut Selector) -> Result<(), DynError> {
    ///     // Add subscribers, servers, etc.
    ///
    ///     // Spin.
    ///     loop {
    ///         selector.wait()?;
    ///     }
    /// }
    /// ```
    pub fn wait(&mut self) -> Result<(), DynError> {
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

        // wait events
        self.wait_timeout()?;

        // notify timers
        self.notify_timer();

        #[cfg(feature = "statistics")]
        {
            // notify subscriptions
            let (target, time_stat) = (&mut self.subscriptions, &mut self.time_stat);
            notify(target, self.wait_set.subscriptions, time_stat);

            // notify services
            let (target, time_stat) = (&mut self.services, &mut self.time_stat);
            notify(target, self.wait_set.services, time_stat);

            // notify clients
            let (target, time_stat) = (&mut self.clients, &mut self.time_stat);
            notify(target, self.wait_set.clients, time_stat);

            // notify guard conditions
            let (target, time_stat) = (&mut self.cond, &mut self.time_stat);
            notify(target, self.wait_set.guard_conditions, time_stat);
        }

        #[cfg(not(feature = "statistics"))]
        {
            // notify subscriptions
            notify(&mut self.subscriptions, self.wait_set.subscriptions);

            // notify services
            notify(&mut self.services, self.wait_set.services);

            // notify clients
            notify(&mut self.clients, self.wait_set.clients);

            // notify guard conditions
            notify(&mut self.cond, self.wait_set.guard_conditions);
        }

        Ok(())
    }

    fn wait_timeout(&mut self) -> Result<(), DynError> {
        if signal_handler::is_halt() {
            return Err("Signaled".into());
        }

        if self.timer.is_empty() {
            #[cfg(feature = "rcl_stat")]
            let wait_start = SystemTime::now();

            // wait forever until arriving events
            rcl::MTSafeFn::rcl_wait(&mut self.wait_set, -1)?;

            #[cfg(feature = "rcl_stat")]
            {
                if let Ok(wait_time) = wait_start.elapsed() {
                    self.time_stat.rcl_wait.add(wait_time);
                }
            }
        } else {
            // insert timer
            let now_time = SystemTime::now();
            let head_delta = *self.timer.front().unwrap().0;
            let timeout = if self.base_time <= now_time {
                let diff = now_time.duration_since(self.base_time).unwrap();
                if diff < head_delta {
                    head_delta - diff
                } else {
                    Duration::ZERO
                }
            } else {
                head_delta + self.base_time.duration_since(now_time).unwrap()
            };

            let timeout_nanos = timeout.as_nanos();
            let timeout_nanos = if timeout_nanos > i64::max_value() as u128 {
                let logger = Logger::new("safe_drive");
                pr_error_in!(
                    logger,
                    "timeout value became too big (overflow): timeout = {timeout_nanos}"
                );
                i64::max_value()
            } else {
                timeout_nanos as i64
            };

            #[cfg(feature = "rcl_stat")]
            let wait_start = SystemTime::now();

            match rcl::MTSafeFn::rcl_wait(&mut self.wait_set, timeout_nanos) {
                Err(RCLError::Timeout) => (),
                Err(e) => return Err(e.into()),
                _ => {
                    #[cfg(feature = "rcl_stat")]
                    {
                        if let Ok(wait_time) = wait_start.elapsed() {
                            self.time_stat.rcl_wait.add(wait_time);
                        }
                    }
                }
            }
        }

        if signal_handler::is_halt() {
            return Err("Signaled".into());
        }

        Ok(())
    }

    fn notify_timer(&mut self) {
        let now_time = SystemTime::now();
        let mut reload = Vec::new(); // wall timer to be reloaded

        while let Some(head) = self.timer.front() {
            if let Some(head_time) = self.base_time.checked_add(*head.0) {
                if head_time < now_time {
                    // pop and execute a callback function
                    let mut dlist = self.timer.pop().unwrap();
                    let head = dlist.front_mut().unwrap();
                    self.base_time += *head.0;

                    let handler = replace(&mut head.1.handler, None);
                    if let Some(mut handler) = handler {
                        #[cfg(feature = "statistics")]
                        let start = std::time::SystemTime::now();

                        handler(); // invoke the callback function

                        // register the wall timer again.
                        if let TimerType::WallTimer(name, dur) = &head.1.event {
                            let elapsed = now_time.elapsed().unwrap();

                            if let Some(dur) = dur.checked_sub(elapsed) {
                                reload.push((name.clone(), dur, handler));
                            } else {
                                reload.push((name.clone(), Duration::ZERO, handler));
                            }

                            #[cfg(feature = "statistics")]
                            if let Ok(elapsed) = start.elapsed() {
                                if let Some(v) = self.time_stat.wall_timer.get_mut(name.as_ref()) {
                                    v.add(elapsed);
                                }
                            }
                        }
                    }
                } else {
                    break;
                }
            }
        }

        // reload wall timers
        for (name, dur, handler) in reload {
            self.add_timer_inner(dur, handler, TimerType::WallTimer(name, dur));
        }
    }
}

impl Drop for Selector {
    fn drop(&mut self) {
        signal_handler::unregister_guard_condition(self.signal_cond.as_ref());
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_wait_set_fini(&mut self.wait_set).unwrap()
    }
}

#[cfg(feature = "statistics")]
fn notify<K, V>(
    m: &mut BTreeMap<*const K, ConditionHandler<V>>,
    array: *const *const K,
    time_stat: &mut TimeStat,
) {
    for i in 0..m.len() {
        unsafe {
            let p = *array.add(i);
            if !p.is_null() {
                debug_assert!(m.contains_key(&p));
                if let Some(h) = m.get_mut(&p) {
                    let mut is_rm = false;
                    if let Some(hdl) = &mut h.handler {
                        let start = std::time::SystemTime::now();

                        let result = hdl();
                        if let Ok(dur) = start.elapsed() {
                            if let Some((_, t)) = time_stat.callback.get_mut(&(p as *const ())) {
                                t.add(dur);
                            }
                        }

                        if result == CallbackResult::Remove {
                            is_rm = true;
                        }
                    }
                    if h.is_once || is_rm {
                        m.remove(&p);
                        time_stat.callback.remove(&(p as *const ()));
                    }
                }
            }
        }
    }
}

#[cfg(not(feature = "statistics"))]
fn notify<K, V>(m: &mut BTreeMap<*const K, ConditionHandler<V>>, array: *const *const K) {
    for i in 0..m.len() {
        unsafe {
            let p = *array.add(i);
            if !p.is_null() {
                debug_assert!(m.contains_key(&p));
                if let Some(h) = m.get_mut(&p) {
                    let mut is_rm = false;
                    if let Some(hdl) = &mut h.handler {
                        if hdl() == CallbackResult::Remove {
                            is_rm = true;
                        }
                    }
                    if h.is_once || is_rm {
                        m.remove(&p);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{context::Context, error::DynError, selector::CallbackResult};
    use std::thread;

    #[test]
    fn test_guard_condition() -> Result<(), DynError> {
        let ctx = Context::new()?;
        let cond = super::GuardCondition::new(ctx.clone())?;

        let ctx2 = ctx.clone();
        let cond2 = cond.clone();

        let w = thread::spawn(move || {
            let mut selector = super::Selector::new(ctx2).unwrap();
            selector.add_guard_condition(
                &cond2,
                Some(Box::new(|| {
                    println!("triggerd!");
                    CallbackResult::Ok
                })),
            );
            selector.wait().unwrap();
        });

        cond.trigger()?;
        w.join().unwrap();

        Ok(())
    }
}
