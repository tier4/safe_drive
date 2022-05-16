use crate::{
    error::{RCLError, RCLResult},
    node::Node,
    qos, rcl,
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
    pub(crate) subscription: Box<rcl::rcl_subscription_t>,
    node: Arc<Node>,
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

pub struct Subscriber<T> {
    pub(crate) subscription: Arc<RCLSubscription>,
    _phantom: PhantomData<T>,
}

impl<T> Subscriber<T> {
    pub fn new(
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
        })
    }

    /// Because is rcl::rcl_take is non-blocking,
    /// try_recv returns Err(RCLError::SubscriberTakeFailed) if
    /// data is not available.
    pub fn try_recv(&self) -> RCLResult<T> {
        rcl_take::<T>(self.subscription.subscription.as_ref())
    }

    pub fn recv(&self) -> AsyncReceiver<T> {
        AsyncReceiver {
            subscription: &self.subscription,
            _phantom: Default::default(),
        }
    }
}

/// Asyncrhonous receiver of subscribers.
pub struct AsyncReceiver<'a, T> {
    subscription: &'a Arc<RCLSubscription>,
    _phantom: PhantomData<T>,
}

impl<'a, T> Future for AsyncReceiver<'a, T> {
    type Output = Result<T, Box<dyn Error>>;

    fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
        // try to take 1 message
        match rcl_take::<T>(self.subscription.subscription.as_ref()) {
            Ok(value) => return Poll::Ready(Ok(value)),  // got
            Err(RCLError::SubscriptionTakeFailed) => (), // no availabe data
            Err(e) => return Poll::Ready(Err(e.into())), // error
        }

        todo!();
        // match self
        //     .subscription
        //     .selector
        //     .select(selector::Op::Subscription(
        //         self.subscription.clone(),
        //         cx.waker().clone(),
        //     )) {
        //     Ok(_) => (),
        //     Err(e) => return Poll::Ready(Err(e.to_string().into())),
        // }

        Poll::Pending
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
