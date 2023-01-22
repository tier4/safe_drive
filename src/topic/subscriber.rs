//! Subscriber to receive messages.
//!
//! When creating a subscriber, you can specify a QoS profile.
//!
//! # Single and Multi Threaded Receive
//!
//! `try_recv` is a non-blocking function to receive.
//! Use `try_recv` in a callback function for single threaded receive.
//!
//! `recv` returns `AsyncReceiver`, which is a future object,
//! and you can use `.await` to receive a message.
//! See the example of `recv`.
//!
//! # Examples
//!
//! ## Single Threaded Execution
//!
//! ```
//! use safe_drive::{
//!     context::Context, logger::Logger, msg::common_interfaces::std_msgs, pr_error, pr_info,
//!     RecvResult,
//! };
//!
//! let ctx = Context::new().unwrap();
//! let node = ctx
//!     .create_node("subscriber_rs_try_recv", None, Default::default())
//!     .unwrap();
//!
//! // Create a subscriber.
//! let subscriber = node
//!     .create_subscriber::<std_msgs::msg::UInt32>("subscriber_rs_try_recv_topic", None)
//!     .unwrap();
//!
//! // Create a publisher.
//! let publisher = node
//!     .create_publisher::<std_msgs::msg::UInt32>("subscriber_rs_try_recv_topic", None)
//!     .unwrap();
//!
//! let logger = Logger::new("subscriber_rs");
//!
//! // Send a message.
//! let mut msg = std_msgs::msg::UInt32::new().unwrap();
//! msg.data = 10;
//! publisher.send(&msg).unwrap();
//!
//! // Receive the message.
//! match subscriber.try_recv() {
//!     RecvResult::Ok(msg) => pr_info!(logger, "msg = {}", msg.data),
//!     RecvResult::RetryLater(_) => pr_info!(logger, "retry later"),
//!     RecvResult::Err(e) => pr_error!(logger, "error = {}", e),
//! }
//! ```
//!
//! ## Multi Threaded Execution
//!
//! ```
//! #[allow(unused_imports)]
//! use async_std::{future, prelude::*};
//! use safe_drive::{
//!     context::Context, logger::Logger, msg::common_interfaces::std_msgs, pr_info, pr_warn,
//!     topic::subscriber::Subscriber,
//! };
//! use std::time::Duration;
//!
//! // Create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create nodes.
//! let node_sub = ctx
//!     .create_node("subscriber_rs_recv", None, Default::default())
//!     .unwrap();
//!
//! // Create a subscriber.
//! let subscriber = node_sub
//!     .create_subscriber::<std_msgs::msg::String>("subscriber_rs_recv_topic", None)
//!     .unwrap();
//!
//! // Create tasks.
//! async_std::task::block_on(async {
//!     let s = async_std::task::spawn(run_subscriber(subscriber));
//!     s.await;
//! });
//!
//! /// The subscriber.
//! async fn run_subscriber(mut s: Subscriber<std_msgs::msg::String>) {
//!     let dur = Duration::from_millis(100);
//!     let logger = Logger::new("subscriber_rs_recv");
//!     for _ in 0..3 {
//!         // receive a message specifying timeout of 100ms
//!         match future::timeout(dur, s.recv()).await {
//!             Ok(Ok(msg)) => {
//!                 // received a message
//!                 pr_info!(logger, "Received (async): msg = {}", msg.data);
//!             }
//!             Ok(Err(e)) => panic!("{}", e), // fatal error
//!             Err(_) => {
//!                 // timeout
//!                 pr_warn!(logger, "Subscribe (async): timeout");
//!                 break;
//!             }
//!         }
//!     }
//! }
//! ```
//!
//! ## Default QoS Profile
//!
//! ```
//! use safe_drive::{
//!     context::Context,
//!     msg::common_interfaces::std_msgs,
//!     qos::policy::HistoryPolicy,
//! };
//!
//! let ctx = Context::new().unwrap();
//! let node = ctx
//! .create_node("subscriber_rs", None, Default::default())
//! .unwrap();
//!
//! // Use default QoS profile.
//! let subscriber = node
//! .create_subscriber::<std_msgs::msg::Empty>("subscriber_rs_topic", None)
//! .unwrap();
//! ```
//!
//! ## Specifying QoS Profile
//!
//! ```
//! use safe_drive::{
//!     context::Context,
//!     msg::common_interfaces::std_msgs,
//!     qos::{policy::HistoryPolicy, Profile},
//! };
//!
//! let ctx = Context::new().unwrap();
//! let node = ctx
//!     .create_node("subscriber_rs", None, Default::default())
//!     .unwrap();
//!
//! // Create a QoS profile.
//! let mut profile = Profile::default();
//! profile.history = HistoryPolicy::KeepAll;
//!
//! // Specify the QoS profile.
//! let subscriber = node
//!     .create_subscriber::<std_msgs::msg::Empty>("subscriber_rs_topic", Some(profile))
//!     .unwrap();
//! ```
//!
//! `None` of the 2nd argument of `create_subscriber` is equivalent to `Some(Profile::default())`.

use crate::{
    error::{DynError, RCLError, RCLResult},
    get_allocator, is_halt,
    msg::TypeSupport,
    node::Node,
    qos, rcl,
    selector::{
        async_selector::{self, SELECTOR},
        CallbackResult,
    },
    signal_handler::Signaled,
    subscriber_loaned_message::SubscriberLoanedMessage,
    PhantomUnsync, RecvResult,
};
use pin_project::{pin_project, pinned_drop};
use std::{
    ffi::CString,
    future::Future,
    marker::PhantomData,
    mem::MaybeUninit,
    os::raw::c_void,
    pin::Pin,
    ptr::null_mut,
    sync::Arc,
    task::{self, Poll},
};

#[cfg(feature = "rcl_stat")]
use crate::helper::statistics::{SerializableTimeStat, TimeStatistics};

#[cfg(feature = "rcl_stat")]
use parking_lot::Mutex;

pub(crate) struct RCLSubscription {
    pub subscription: Box<rcl::rcl_subscription_t>,

    topic_name: String,

    #[cfg(feature = "rcl_stat")]
    pub latency_take: Mutex<TimeStatistics<4096>>,
    pub node: Arc<Node>,
}

#[cfg(feature = "rcl_stat")]
impl RCLSubscription {
    fn measure_latency(&self, start: std::time::SystemTime) {
        if let Ok(dur) = start.elapsed() {
            let mut guard = self.latency_take.lock();
            guard.add(dur);
        }
    }
}

impl Drop for RCLSubscription {
    fn drop(&mut self) {
        let (node, subscription) = (&mut self.node, &mut self.subscription);
        let guard = rcl::MT_UNSAFE_FN.lock();
        let _ = guard.rcl_subscription_fini(subscription.as_mut(), unsafe { node.as_ptr_mut() });
    }
}

unsafe impl Sync for RCLSubscription {}
unsafe impl Send for RCLSubscription {}

/// Subscriber.
pub struct Subscriber<T> {
    pub(crate) subscription: Arc<RCLSubscription>,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: TypeSupport> Subscriber<T> {
    pub(crate) fn new(
        node: Arc<Node>,
        topic_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Self> {
        let mut subscription = Box::new(rcl::MTSafeFn::rcl_get_zero_initialized_subscription());

        let topic_name_c = CString::new(topic_name).unwrap_or_default();
        let options = Options::new(&qos.unwrap_or_default());

        {
            let guard = rcl::MT_UNSAFE_FN.lock();

            guard.rcl_subscription_init(
                subscription.as_mut(),
                node.as_ptr(),
                T::type_support(),
                topic_name_c.as_ptr(),
                options.as_ptr(),
            )?;
        }

        Ok(Subscriber {
            subscription: Arc::new(RCLSubscription {
                subscription,
                node,
                topic_name: topic_name.to_string(),

                #[cfg(feature = "rcl_stat")]
                latency_take: Mutex::new(TimeStatistics::new()),
            }),
            _phantom: Default::default(),
            _unsync: Default::default(),
        })
    }

    pub fn get_topic_name(&self) -> &str {
        &self.subscription.topic_name
    }

    /// Non-blocking receive.
    ///
    /// Because `rcl::rcl_take` is non-blocking,
    /// `try_recv()` returns `RecvResult::RetryLater` if
    /// data is not available.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_msgs, pr_error, pr_info,
    ///     topic::subscriber::Subscriber, RecvResult,
    /// };
    ///
    /// fn pubsub(subscriber: Subscriber<std_msgs::msg::UInt32>, logger: Logger) {
    ///     // Receive the message.
    ///     match subscriber.try_recv() {
    ///         RecvResult::Ok(msg) => pr_info!(logger, "msg = {}", msg.data),
    ///         RecvResult::RetryLater(_) => pr_info!(logger, "retry later"),
    ///         RecvResult::Err(e) => pr_error!(logger, "error = {}", e),
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::SubscriptionInvalid` if the subscription is invalid, or
    /// - `RCLError::BadAlloc if allocating` memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    #[must_use]
    pub fn try_recv(&self) -> RecvResult<TakenMsg<T>, ()> {
        #[cfg(feature = "rcl_stat")]
        let start = std::time::SystemTime::now();

        let s = self.subscription.clone();
        match take::<T>(&s) {
            Ok(n) => {
                #[cfg(feature = "rcl_stat")]
                self.subscription.measure_latency(start);

                RecvResult::Ok(n)
            }
            Err(RCLError::SubscriptionTakeFailed) => {
                #[cfg(feature = "rcl_stat")]
                self.subscription.measure_latency(start);

                RecvResult::RetryLater(())
            }
            Err(e) => RecvResult::Err(e.into()),
        }
    }

    /// Receive a message asynchronously.
    ///
    /// This waits and blocks forever until a message arrives.
    /// In order to call `recv()` with timeout,
    /// use mechanisms provided by asynchronous libraries,
    /// such as `async_std::future::timeout`.
    ///
    /// # Example
    ///
    /// ```
    /// #[allow(unused_imports)]
    /// use async_std::{future, prelude::*};
    /// use safe_drive::{
    ///     logger::Logger, msg::common_interfaces::std_msgs, pr_info, pr_warn,
    ///     topic::subscriber::Subscriber,
    /// };
    /// use std::time::Duration;
    ///
    /// async fn run_subscriber(mut s: Subscriber<std_msgs::msg::String>) {
    ///     let dur = Duration::from_millis(100);
    ///     let logger = Logger::new("subscriber_rs_recv");
    ///     for _ in 0..3 {
    ///         // receive a message specifying timeout of 100ms
    ///         match future::timeout(dur, s.recv()).await {
    ///             Ok(Ok(msg)) => {
    ///                 // received a message
    ///                 pr_info!(logger, "Received (async): msg = {}", msg.data);
    ///             }
    ///             Ok(Err(e)) => panic!("{}", e), // fatal error
    ///             Err(_) => {
    ///                 // timeout
    ///                 pr_warn!(logger, "Subscribe (async): timeout");
    ///                 break;
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::SubscriptionInvalid` if the subscription is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub async fn recv(&mut self) -> Result<TakenMsg<T>, DynError> {
        AsyncReceiver {
            subscription: &mut self.subscription,
            is_waiting: false,
            _phantom: Default::default(),
        }
        .await
    }

    /// Get latency statistics information of `Mutex` and `rcl_take()`.
    /// Because `rcl_take()` is MT-UNSAFE, a latency includes not only `rcl_take` but also `Mutex`.
    #[cfg(feature = "rcl_stat")]
    pub fn statistics(&self) -> SerializableTimeStat {
        let guard = self.subscription.latency_take.lock();
        guard.to_serializable()
    }
}

/// Asynchronous receiver of subscribers.
#[pin_project(PinnedDrop)]
pub struct AsyncReceiver<'a, T> {
    subscription: &'a mut Arc<RCLSubscription>,
    is_waiting: bool,
    _phantom: PhantomData<T>,
}

impl<'a, T> Future for AsyncReceiver<'a, T> {
    type Output = Result<TakenMsg<T>, DynError>;

    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err(Signaled.into()));
        }

        let this = self.project();

        let s = this.subscription.clone();

        // let is_waiting = this.is_waiting;
        // let subscription = this.subscription;
        *this.is_waiting = false;

        #[cfg(feature = "rcl_stat")]
        let start = std::time::SystemTime::now();

        // try to take 1 message
        match take::<T>(&s) {
            Ok(value) => {
                #[cfg(feature = "rcl_stat")]
                subscription.measure_latency(start);

                Poll::Ready(Ok(value))
            } // got
            Err(RCLError::SubscriptionTakeFailed) => {
                #[cfg(feature = "rcl_stat")]
                subscription.measure_latency(start);

                let mut guard = SELECTOR.lock();
                let mut waker = Some(cx.waker().clone());

                guard.send_command(
                    &this.subscription.node.context,
                    async_selector::Command::Subscription(
                        this.subscription.clone(),
                        Box::new(move || {
                            let w = waker.take();
                            w.unwrap().wake();
                            CallbackResult::Ok
                        }),
                    ),
                )?;

                *this.is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e.into())), // error
        }
    }
}

#[pinned_drop]
impl<'a, T> PinnedDrop for AsyncReceiver<'a, T> {
    fn drop(self: Pin<&mut Self>) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            let _ = guard.send_command(
                &self.subscription.node.context,
                async_selector::Command::RemoveSubscription(self.subscription.clone()),
            );
        }
    }
}

/// Options for subscribers.
struct Options {
    options: rcl::rcl_subscription_options_t,
}

impl Options {
    fn new(qos: &qos::Profile) -> Self {
        let options = rcl::rcl_subscription_options_t {
            qos: qos.into(),
            allocator: get_allocator(),
            rmw_subscription_options: rcl::MTSafeFn::rmw_get_default_subscription_options(),
        };
        Options { options }
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_subscription_options_t {
        &self.options
    }
}

/// A smart pointer for the message taken from the topic with `rcl_take` or `rcl_take_loaned_message`.
pub enum TakenMsg<T> {
    Copied(T),
    Loaned(SubscriberLoanedMessage<T>),
}

impl<T> TakenMsg<T> {
    // Returns the owned message without cloning if the subscriber owns the memory region and its data. None is returned when it does not own the memory region (i.e. the message is loaned).
    pub fn get_owned(self) -> Option<T> {
        match self {
            TakenMsg::Copied(inner) => Some(inner),
            TakenMsg::Loaned(_) => None,
        }
    }
}

impl<T> std::ops::Deref for TakenMsg<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            TakenMsg::Copied(copied) => copied,
            TakenMsg::Loaned(loaned) => loaned.get(),
        }
    }
}

impl<T> std::ops::DerefMut for TakenMsg<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            TakenMsg::Copied(copied) => copied,
            TakenMsg::Loaned(loaned) => loaned.get(),
        }
    }
}

fn take<T>(subscription: &Arc<RCLSubscription>) -> RCLResult<TakenMsg<T>> {
    if rcl::MTSafeFn::rcl_subscription_can_loan_messages(subscription.subscription.as_ref()) {
        take_loaned_message(subscription.clone()).map(TakenMsg::Loaned)
    } else {
        rcl_take(subscription.subscription.as_ref()).map(TakenMsg::Copied)
    }
}

fn take_loaned_message<T>(
    subscription: Arc<RCLSubscription>,
) -> RCLResult<SubscriberLoanedMessage<T>> {
    let guard = rcl::MT_UNSAFE_FN.lock();
    let message: *mut T = null_mut();
    guard
        .rcl_take_loaned_message(
            subscription.subscription.as_ref(),
            &message as *const _ as *mut _,
            null_mut(),
            null_mut(),
        )
        .map(|_| SubscriberLoanedMessage::new(subscription, message))
}

fn rcl_take<T>(subscription: &rcl::rcl_subscription_t) -> RCLResult<T> {
    let guard = rcl::MT_UNSAFE_FN.lock();
    let mut ros_message: T = unsafe { MaybeUninit::zeroed().assume_init() };
    match guard.rcl_take(
        subscription,
        &mut ros_message as *mut _ as *mut c_void,
        null_mut(),
        null_mut(),
    ) {
        Ok(_) => Ok(ros_message),
        Err(e) => Err(e),
    }
}
