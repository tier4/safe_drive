use crate::{
    context::Context,
    error::{ret_val_to_err, RCLResult},
    rcl,
};
use std::{
    ffi::CString,
    sync::{Arc, Mutex},
};

pub struct Node {
    node: rcl::rcl_node_t,
    _context: Arc<Mutex<Context>>,
}

impl Node {
    pub fn new(
        context: Arc<Mutex<Context>>,
        name: &str,
        namespace: Option<&str>,
        options: NodeOptions,
    ) -> RCLResult<Self> {
        let mut node = unsafe { rcl::rcl_get_zero_initialized_node() };

        let name = CString::new(name).unwrap();
        let namespace = CString::new(namespace.unwrap_or_default()).unwrap();

        {
            let mut guard = context.lock().unwrap();
            ret_val_to_err(unsafe {
                rcl::rcl_node_init(
                    &mut node,
                    name.as_ptr(),
                    namespace.as_ptr(),
                    guard.as_ptr_mut(),
                    options.as_ptr(),
                )
            })?;
        }

        Ok(Node {
            node,
            _context: context,
        })
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_node_t {
        &self.node
    }

    pub(crate) fn as_ptr_mut(&mut self) -> *mut rcl::rcl_node_t {
        &mut self.node
    }
}

impl Drop for Node {
    fn drop(&mut self) {
        ret_val_to_err(unsafe { rcl::rcl_node_fini(&mut self.node) }).unwrap();
    }
}

/// Options for nodes.
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
