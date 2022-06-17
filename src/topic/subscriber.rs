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
//! ## Single and Multi Threaded Execution
//!
//! See [Subscriber].
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
    is_halt,
    msg::TopicMsg,
    node::Node,
    qos, rcl,
    selector::async_selector::{self, SELECTOR},
    PhantomUnsync,
};
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

pub(crate) struct RCLSubscription {
    pub subscription: Box<rcl::rcl_subscription_t>,
    pub node: Arc<Node>,
}

impl Drop for RCLSubscription {
    fn drop(&mut self) {
        let (node, subscription) = (&mut self.node, &mut self.subscription);
        let guard = rcl::MT_UNSAFE_FN.lock();

        guard
            .rcl_subscription_fini(subscription.as_mut(), unsafe { node.as_ptr_mut() })
            .unwrap();
    }
}

unsafe impl Sync for RCLSubscription {}
unsafe impl Send for RCLSubscription {}

/// Subscriber.
///
/// # Example
///
/// ```
/// use safe_drive::{
///     context::Context, error::RCLError, logger::Logger, msg::common_interfaces::std_msgs,
///     pr_error, pr_info,
/// };
///
/// let ctx = Context::new().unwrap();
/// let node = ctx
///     .create_node("subscriber_rs", None, Default::default())
///     .unwrap();
/// let logger = Logger::new("subscriber_rs");
///
/// // Create a subscriber.
/// let subscriber = node
///     .create_subscriber::<std_msgs::msg::UInt32>("subscriber_rs_topic", None)
///     .unwrap();
///
/// // Non-blocking receive.
/// match subscriber.try_recv() {
///     Ok(msg) => pr_info!(logger, "Receive: msg = {}", msg.data),
///     Err(RCLError::SubscriptionTakeFailed) => {
///         pr_info!(logger, "Receive: No available Data")
///     }
///     Err(e) => {
///         pr_error!(logger, "Receive: Error = {e}")
///     }
/// }
/// ```
pub struct Subscriber<T> {
    pub(crate) subscription: Arc<RCLSubscription>,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T: TopicMsg> Subscriber<T> {
    pub(crate) fn new(
        node: Arc<Node>,
        topic_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Self> {
        let mut subscription = Box::new(rcl::MTSafeFn::rcl_get_zero_initialized_subscription());

        let topic_name = CString::new(topic_name).unwrap_or_default();
        let options = Options::new(&qos.unwrap_or_default());

        {
            let guard = rcl::MT_UNSAFE_FN.lock();

            guard.rcl_subscription_init(
                subscription.as_mut(),
                node.as_ptr(),
                T::type_support(),
                topic_name.as_ptr(),
                options.as_ptr(),
            )?;
        }

        Ok(Subscriber {
            subscription: Arc::new(RCLSubscription { subscription, node }),
            _phantom: Default::default(),
            _unsync: Default::default(),
        })
    }

    /// Non-blocking receive.
    ///
    /// Because `rcl::rcl_take` is non-blocking,
    /// `try_recv()` returns `Err(RCLError::SubscriberTakeFailed)` if
    /// data is not available.
    /// So, please retry later if `Err(RCLError::SubscriberTakeFailed)` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use std::{cell::RefCell, rc::Rc, time::Duration};
    /// use safe_drive::{
    ///     context::Context, error::RCLError, logger::Logger, msg::common_interfaces::std_msgs,
    ///     pr_error, pr_info,
    /// };
    ///
    /// let ctx = Context::new().unwrap();
    /// let node = ctx
    ///     .create_node("subscriber_rs_try_recv", None, Default::default())
    ///     .unwrap();
    /// let logger = Logger::new("subscriber_rs_try_recv");
    /// let mut selector = ctx.create_selector().unwrap();
    ///
    /// // Create a subscriber.
    /// let subscriber = node
    ///     .create_subscriber::<std_msgs::msg::UInt32>("subscriber_rs_try_recv_topic", None)
    ///     .unwrap();
    ///
    /// let sub1 = Rc::new(RefCell::new(subscriber));
    /// let sub2 = sub1.clone();
    ///
    /// let logger1 = Rc::new(RefCell::new(logger));
    /// let logger2 = logger1.clone();
    ///
    /// // Register the subscriber to the selector.
    /// selector.add_subscriber(
    ///     &sub1.borrow(),
    ///     Some(Box::new(move || {
    ///         let sub = sub2.borrow();
    ///         let logger = logger1.borrow();
    ///         loop {
    ///             match sub.try_recv() {
    ///                 Ok(msg) => pr_info!(logger, "Receive: msg = {}", msg.data),
    ///                 Err(RCLError::SubscriptionTakeFailed) => {
    ///                     pr_info!(logger, "Receive: No available Data");
    ///                     break;
    ///                 }
    ///                 Err(e) => {
    ///                     pr_error!(logger, "Receive: Error = {e}");
    ///                     break;
    ///                 }
    ///             }
    ///         }
    ///     })),
    ///     false,
    /// );
    ///
    /// // Add a wall timer.
    /// selector.add_wall_timer(
    ///     Duration::from_millis(100),
    ///     Box::new(move || {
    ///         let logger = logger2.borrow();
    ///         pr_info!(logger, "Receive: Timeout")
    ///     }),
    /// );
    ///
    /// // Spin.
    /// for _ in 0..3 {
    ///     selector.wait().unwrap();
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::SubscriptionInvalid` if the subscription is invalid, or
    /// - `RCLError::BadAlloc if allocating` memory failed, or
    /// - `RCLError::SubscriptionTakeFailed` if take failed but *no error* occurred in the middleware, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn try_recv(&self) -> RCLResult<T> {
        rcl_take::<T>(self.subscription.subscription.as_ref())
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
    ///     context::Context, logger::Logger, msg::common_interfaces::std_msgs, pr_info, pr_warn,
    ///     topic::subscriber::Subscriber,
    /// };
    /// use std::time::Duration;
    ///
    /// // Create a context.
    /// let ctx = Context::new().unwrap();
    ///
    /// // Create nodes.
    /// let node_sub = ctx
    ///     .create_node("subscriber_rs_recv", None, Default::default())
    ///     .unwrap();
    ///
    /// // Create a subscriber.
    /// let subscriber = node_sub
    ///     .create_subscriber::<std_msgs::msg::String>("subscriber_rs_recv_topic", None)
    ///     .unwrap();
    ///
    /// // Create tasks.
    /// async_std::task::block_on(async {
    ///     let s = async_std::task::spawn(run_subscriber(subscriber));
    ///     s.await;
    /// });
    ///
    /// /// The subscriber.
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
    pub async fn recv(&mut self) -> Result<T, DynError> {
        AsyncReceiver {
            subscription: &mut self.subscription,
            is_waiting: false,
            _phantom: Default::default(),
        }
        .await
    }
}

/// Asynchronous receiver of subscribers.
pub struct AsyncReceiver<'a, T> {
    subscription: &'a mut Arc<RCLSubscription>,
    is_waiting: bool,
    _phantom: PhantomData<T>,
}

impl<'a, T> Future for AsyncReceiver<'a, T> {
    type Output = Result<T, DynError>;

    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        if is_halt() {
            return Poll::Ready(Err("Signaled".into()));
        }

        let (is_waiting, subscription) = unsafe {
            let this = self.get_unchecked_mut();
            (&mut this.is_waiting, &this.subscription)
        };
        *is_waiting = false;

        let s = subscription.subscription.as_ref();

        // try to take 1 message
        match rcl_take::<T>(s) {
            Ok(value) => Poll::Ready(Ok(value)), // got
            Err(RCLError::SubscriptionTakeFailed) => {
                let mut guard = SELECTOR.lock();
                let waker = cx.waker().clone();

                guard.send_command(
                    &subscription.node.context,
                    async_selector::Command::Subscription(
                        (*subscription).clone(),
                        Box::new(move || waker.clone().wake()),
                    ),
                )?;

                *is_waiting = true;
                Poll::Pending
            }
            Err(e) => Poll::Ready(Err(e.into())), // error
        }
    }
}

impl<'a, T> Drop for AsyncReceiver<'a, T> {
    fn drop(&mut self) {
        if self.is_waiting {
            let mut guard = SELECTOR.lock();
            guard
                .send_command(
                    &self.subscription.node.context,
                    async_selector::Command::RemoveSubscription(self.subscription.clone()),
                )
                .unwrap();
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
            allocator: rcl::MTSafeFn::rcutils_get_default_allocator(),
            rmw_subscription_options: rcl::MTSafeFn::rmw_get_default_subscription_options(),
        };
        Options { options }
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_subscription_options_t {
        &self.options
    }
}

fn rcl_take<T>(subscription: &rcl::rcl_subscription_t) -> RCLResult<T> {
    let mut ros_message: T = unsafe { MaybeUninit::zeroed().assume_init() };

    let guard = rcl::MT_UNSAFE_FN.lock();
    guard.rcl_take(
        subscription,
        &mut ros_message as *mut _ as *mut c_void,
        null_mut(),
        null_mut(),
    )?;

    Ok(ros_message)
}
