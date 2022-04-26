use crate::{error::ret_val_to_err, rcl};

/// Options for a node
pub struct NodeOptions {
    options: rcl::rcl_node_options_t,
}

impl Default for NodeOptions {
    fn default() -> Self {
        let options = unsafe { rcl::rcl_node_get_default_options() };
        NodeOptions { options }
    }
}

impl NodeOptions {
    /// Create options to create a node
    pub fn new() -> Self {
        // TODO: allow setting options
        Default::default()
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_node_options_t {
        &self.options
    }
}

impl Drop for NodeOptions {
    fn drop(&mut self) {
        ret_val_to_err(unsafe { rcl::rcl_node_options_fini(&mut self.options) }).unwrap();
    }
}
