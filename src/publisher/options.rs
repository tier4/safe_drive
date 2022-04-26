use crate::{qos, rcl};

pub struct Options {
    options: rcl::rcl_publisher_options_t,
}

impl Options {
    pub fn new(qos: &qos::Profile) -> Self {
        let options = rcl::rcl_publisher_options_t {
            qos: qos.into(),
            allocator: unsafe { rcl::rcutils_get_default_allocator() },
            rmw_publisher_options: unsafe { rcl::rmw_get_default_publisher_options() },
        };
        Options { options }
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_publisher_options_t {
        &self.options
    }
}
