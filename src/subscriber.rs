use crate::{
    error::{ret_val_to_err, RCLResult},
    node::Node,
    qos, rcl,
};
use std::{
    ffi::{c_void, CString},
    marker::PhantomData,
    mem::MaybeUninit,
    ptr::null_mut,
    sync::{Arc, Mutex},
};

pub struct Subscriber<T> {
    subscription: rcl::rcl_subscription_t,
    node: Arc<Mutex<Node>>,
    _phantom: PhantomData<T>,
}

impl<T> Subscriber<T> {
    pub fn new(
        node: Arc<Mutex<Node>>,
        topic_name: &str,
        type_support: *const (),
        qos: Option<qos::Profile>,
    ) -> RCLResult<Self> {
        let mut subscription = unsafe { rcl::rcl_get_zero_initialized_subscription() };

        let topic_name = CString::new(topic_name).unwrap_or_default();
        let options = Options::new(&qos.unwrap_or_default());

        ret_val_to_err(unsafe {
            rcl::rcl_subscription_init(
                &mut subscription,
                node.lock().unwrap().as_ptr(),
                type_support as _,
                topic_name.as_ptr(),
                options.as_ptr(),
            )
        })?;

        Ok(Subscriber {
            subscription,
            node,
            _phantom: Default::default(),
        })
    }

    /// Because is rcl::rcl_take is non-blocking,
    /// recv returns Err(RCLError::SubscriberTakeFailed) if
    /// data is not available.
    pub fn recv(&self) -> RCLResult<T> {
        let mut ros_message: T = unsafe { MaybeUninit::zeroed().assume_init() };

        ret_val_to_err(unsafe {
            rcl::rcl_take(
                &self.subscription,
                &mut ros_message as *mut _ as *mut c_void,
                null_mut(),
                null_mut(),
            )
        })?;

        Ok(ros_message)
    }
}

impl<T> Drop for Subscriber<T> {
    fn drop(&mut self) {
        let (node, subscription) = (&mut self.node, &mut self.subscription);
        ret_val_to_err(unsafe {
            rcl::rcl_subscription_fini(subscription, node.lock().unwrap().as_ptr_mut())
        })
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
            allocator: unsafe { rcl::rcutils_get_default_allocator() },
            rmw_subscription_options: unsafe { rcl::rmw_get_default_subscription_options() },
        };
        Options { options }
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_subscription_options_t {
        &self.options
    }
}
