use crate::{qos, rcl};

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
