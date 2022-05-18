use crate::{
    error::{RCLError, RCLResult},
    node::Node,
    qos, rcl,
    selector::async_selector::{self, SELECTOR},
    PhantomUnsync,
};
use std::{
    error::Error,
    ffi::{c_void, CString},
    future::Future,
    marker::PhantomData,
    mem::MaybeUninit,
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
        let guard = rcl::MT_UNSAFE_FN.lock().unwrap();

        guard
            .rcl_subscription_fini(subscription.as_mut(), unsafe { node.as_ptr_mut() })
            .unwrap();
    }
}

unsafe impl Sync for RCLSubscription {}
unsafe impl Send for RCLSubscription {}

pub struct Subscriber<T> {
    pub(crate) subscription: Arc<RCLSubscription>,
    _phantom: PhantomData<T>,
    _unsync: PhantomUnsync,
}

impl<T> Subscriber<T> {
    pub(crate) fn new(
        node: Arc<Node>,
        topic_name: &str,
        type_support: *const (),
        qos: Option<qos::Profile>,
    ) -> RCLResult<Self> {
        let mut subscription = Box::new(rcl::MTSafeFn::rcl_get_zero_initialized_subscription());

        let topic_name = CString::new(topic_name).unwrap_or_default();
        let options = Options::new(&qos.unwrap_or_default());

        {
            let guard = rcl::MT_UNSAFE_FN.lock().unwrap();

            guard.rcl_subscription_init(
                subscription.as_mut(),
                node.as_ptr(),
                type_support as _,
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

    /// Because `rcl::rcl_take` is non-blocking,
    /// `try_recv()` returns `Err(RCLError::SubscriberTakeFailed)` if
    /// data is not available.
    /// So, please retry later if `Err(RCLError::SubscriberTakeFailed)` is returned.
    ///
    /// Errors:
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
    /// This waits and blocks forever until a message arrives.
    /// In order to call `recv()` with timeout,
    /// use mechanisms provided by asynchronous libraries,
    /// such as `async_std::future::timeout`.
    ///
    /// Errors:
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::SubscriptionInvalid` if the subscription is invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn recv(&mut self) -> AsyncReceiver<T> {
        AsyncReceiver {
            subscription: &mut self.subscription,
            _phantom: Default::default(),
        }
    }
}

/// Asynchronous receiver of subscribers.
pub struct AsyncReceiver<'a, T> {
    subscription: &'a mut Arc<RCLSubscription>,
    _phantom: PhantomData<T>,
}

impl<'a, T> Future for AsyncReceiver<'a, T> {
    type Output = Result<T, Box<dyn Error + Send + Sync + 'static>>;

    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        let s = self.subscription.subscription.as_ref();

        // try to take 1 message
        match rcl_take::<T>(s) {
            Ok(value) => return Poll::Ready(Ok(value)),  // got
            Err(RCLError::SubscriptionTakeFailed) => (), // no availabe data
            Err(e) => return Poll::Ready(Err(e.into())), // error
        }

        let mut guard = SELECTOR.lock().unwrap();
        let waker = cx.waker().clone();

        guard.send_command(
            &self.subscription.node.context,
            async_selector::Command::Subscription(
                self.subscription.clone(),
                Box::new(move || waker.clone().wake()),
            ),
        )?;

        Poll::Pending
    }
}

impl<'a, T> Drop for AsyncReceiver<'a, T> {
    fn drop(&mut self) {
        let mut guard = SELECTOR.lock().unwrap();
        guard
            .send_command(
                &self.subscription.node.context,
                async_selector::Command::RemoveSubscription(self.subscription.clone()),
            )
            .unwrap();
    }
}

/// Options for subscribers.
pub struct Options {
    options: rcl::rcl_subscription_options_t,
}

impl Options {
    pub fn new(qos: &qos::Profile) -> Self {
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

    let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
    guard.rcl_take(
        subscription,
        &mut ros_message as *mut _ as *mut c_void,
        null_mut(),
        null_mut(),
    )?;

    Ok(ros_message)
}
