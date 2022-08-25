//! Publisher to publish messages.
//!
//! When creating publisher, you can specify a QoS profile.
//!
//! # Examples
//!
//! ## Default QoS Profile
//!
//! ```
//! use safe_drive::{context::Context, msg::common_interfaces::std_msgs};
//!
//! let ctx = Context::new().unwrap();
//! let node_pub = ctx
//!     .create_node("publisher_rs", None, Default::default())
//!     .unwrap();
//!
//! // Create a publisher.
//! let publisher = node_pub
//!     .create_publisher::<std_msgs::msg::UInt32>("publisher_rs_topic", None)
//!     .unwrap();
//!
//! // Send a message.
//! let mut msg = std_msgs::msg::UInt32::new().unwrap();
//! msg.data = 1234;
//! publisher.send(&msg).unwrap();
//! ```
//!
//! ## Specifying QoS Profile
//!
//! ```
//! use safe_drive::{context::Context, msg::common_interfaces::std_msgs, qos::{Profile, policy::HistoryPolicy}};
//!
//! let ctx = Context::new().unwrap();
//! let node_pub = ctx
//!     .create_node("publisher_rs_qos", None, Default::default())
//!     .unwrap();
//!
//! // Create a QoS policy.
//! let mut profile = Profile::default();
//! profile.history = HistoryPolicy::KeepAll;
//!
//! // Create a publisher with the QoS profile.
//! let publisher = node_pub
//!     .create_publisher::<std_msgs::msg::UInt32>("publisher_rs_topic_qos", Some(profile))
//!     .unwrap();
//! ```
//!
//! `None` of the 2nd argument of `create_publisher` is equivalent to `Some(Profile::default())`.

use crate::{
    error::{DynError, RCLResult},
    msg::TopicMsg,
    node::Node,
    qos, rcl,
    signal_handler::Signaled,
};
use std::{ffi::CString, marker::PhantomData, ptr::null_mut, sync::Arc};

#[cfg(feature = "rcl_stat")]
use crate::helper::statistics::{SerializableTimeStat, TimeStatistics};

#[cfg(feature = "rcl_stat")]
use parking_lot::Mutex;

/// Publisher.
///
/// # Example
///
/// ```
/// use safe_drive::{context::Context, msg::common_interfaces::std_msgs};
///
/// let ctx = Context::new().unwrap();
/// let node_pub = ctx
///     .create_node("publish_rs", None, Default::default())
///     .unwrap();
///
/// // Create a publisher.
/// let publisher = node_pub
///     .create_publisher::<std_msgs::msg::UInt32>("publish_rs_topic", None)
///     .unwrap();
///
/// // Send a message.
/// let mut msg = std_msgs::msg::UInt32::new().unwrap();
/// msg.data = 1234;
/// publisher.send(&msg).unwrap();
/// ```
pub struct Publisher<T> {
    publisher: rcl::rcl_publisher_t,
    topic_name: String,

    #[cfg(feature = "rcl_stat")]
    latency_publish: Mutex<TimeStatistics<4096>>,

    _phantom: PhantomData<T>,
    node: Arc<Node>,
}

impl<T: TopicMsg> Publisher<T> {
    pub(crate) fn new(
        node: Arc<Node>,
        topic_name: &str,
        qos: Option<qos::Profile>,
    ) -> RCLResult<Self> {
        let mut publisher = rcl::MTSafeFn::rcl_get_zero_initialized_publisher();

        let topic_name_c = CString::new(topic_name).unwrap_or_default();
        let options = Options::new(&qos.unwrap_or_default());

        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_publisher_init(
                &mut publisher,
                node.as_ptr(),
                T::type_support(),
                topic_name_c.as_ptr(),
                options.as_ptr(),
            )?;
        }

        Ok(Publisher {
            publisher,
            node,
            topic_name: topic_name.to_string(),

            #[cfg(feature = "rcl_stat")]
            latency_publish: Mutex::new(TimeStatistics::new()),

            _phantom: Default::default(),
        })
    }

    pub fn get_topic_name(&self) -> &str {
        &self.topic_name
    }

    /// Send a message.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::{context::Context, msg::common_interfaces::std_msgs};
    ///
    /// let ctx = Context::new().unwrap();
    /// let node = ctx
    ///     .create_node("publish_rs_send", None, Default::default())
    ///     .unwrap();
    ///
    /// // Create a publisher.
    /// let publisher = node.create_publisher("publish_rs_send_topic", None).unwrap();
    ///
    /// // Send a message.
    /// let msg = std_msgs::msg::Empty::new().unwrap();
    /// publisher.send(&msg).unwrap();
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::PublisherInvalid` if the publisher is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn send(&self, msg: &T) -> Result<(), DynError> {
        if crate::is_halt() {
            return Err(Signaled.into());
        }

        #[cfg(feature = "rcl_stat")]
        let start = std::time::SystemTime::now();

        if let Err(e) =
            rcl::MTSafeFn::rcl_publish(&self.publisher, msg as *const T as _, null_mut())
        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcutils_reset_error();
            return Err(e.into());
        }

        #[cfg(feature = "rcl_stat")]
        {
            if let Ok(dur) = start.elapsed() {
                let mut guard = self.latency_publish.lock();
                guard.add(dur);
            }
        }

        Ok(())
    }

    /// Get latency statistics information of `rcl_publish()`.
    #[cfg(feature = "rcl_stat")]
    pub fn statistics(&self) -> SerializableTimeStat {
        let guard = self.latency_publish.lock();
        guard.to_serializable()
    }
}

impl<T> Drop for Publisher<T> {
    fn drop(&mut self) {
        let (node, publisher) = (&mut self.node, &mut self.publisher);
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard
            .rcl_publisher_fini(publisher, unsafe { node.as_ptr_mut() })
            .unwrap();
    }
}

/// Options for publishers.
struct Options {
    options: rcl::rcl_publisher_options_t,
}

impl Options {
    fn new(qos: &qos::Profile) -> Self {
        let options = rcl::rcl_publisher_options_t {
            qos: qos.into(),
            allocator: rcl::MTSafeFn::rcutils_get_default_allocator(),
            rmw_publisher_options: rcl::MTSafeFn::rmw_get_default_publisher_options(),
        };
        Options { options }
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_publisher_options_t {
        &self.options
    }
}

unsafe impl<T> Sync for Publisher<T> {}
unsafe impl<T> Send for Publisher<T> {}
