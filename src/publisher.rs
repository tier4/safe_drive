use crate::{error::RCLResult, node::Node, qos, rcl};
use std::{ffi::CString, marker::PhantomData, ptr::null_mut, sync::Arc};

pub struct Publisher<T> {
    publisher: rcl::rcl_publisher_t,
    node: Arc<Node>,
    _phantom: PhantomData<T>,
}

impl<T> Publisher<T> {
    pub fn new(
        node: Arc<Node>,
        topic_name: &str,
        type_support: *const (),
        qos: Option<qos::Profile>,
    ) -> RCLResult<Self> {
        let mut publisher = rcl::MTSafeFn::rcl_get_zero_initialized_publisher();

        let topic_name = CString::new(topic_name).unwrap_or_default();
        let options = Options::new(&qos.unwrap_or_default());

        {
            let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
            guard.rcl_publisher_init(
                &mut publisher,
                node.as_ptr(),
                type_support as _,
                topic_name.as_ptr(),
                options.as_ptr(),
            )?;
        }

        Ok(Publisher {
            publisher,
            node,
            _phantom: Default::default(),
        })
    }

    pub fn send(&self, msg: T) -> RCLResult<()> {
        rcl::MTSafeFn::rcl_publish(&self.publisher, &msg as *const T as _, null_mut())?;
        Ok(())
    }
}

impl<T> Drop for Publisher<T> {
    fn drop(&mut self) {
        let (node, publisher) = (&mut self.node, &mut self.publisher);
        let guard = rcl::MT_UNSAFE_FN.lock().unwrap();
        guard
            .rcl_publisher_fini(publisher, unsafe { node.as_ptr_mut() })
            .unwrap();
    }
}

/// Options for publishers.
pub struct Options {
    options: rcl::rcl_publisher_options_t,
}

impl Options {
    pub fn new(qos: &qos::Profile) -> Self {
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
