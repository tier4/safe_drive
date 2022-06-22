//! Context of ROS2.
//! A context can create `Node` and `Selector`.
//!
//! # Example
//!
//! ```
//! use safe_drive::context::Context;
//!
//! // Create a context.
//! let ctx = Context::new().unwrap();
//!
//! // Create a node.
//! let node = ctx
//!     .create_node("context_rs", None, Default::default())
//!     .unwrap();
//!
//! // Create a selector.
//! let selector = ctx.create_selector().unwrap();
//! ```

use crate::{
    error::*,
    node::{Node, NodeOptions},
    rcl,
    selector::{async_selector::SELECTOR, Selector},
    signal_handler,
};
use once_cell::sync::Lazy;
use parking_lot::Mutex;
use std::{collections::BTreeSet, env, ffi::CString, sync::Arc};

pub static ID_CONTEXT: Lazy<Mutex<BTreeSet<usize>>> = Lazy::new(|| Mutex::new(BTreeSet::new()));

/// Context of ROS2.
pub struct Context {
    context: rcl::rcl_context_t,
    pub(crate) id: usize,
}

impl Context {
    /// Create a new context.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::context::Context;
    ///
    /// // Create a context.
    /// let ctx = Context::new().unwrap();
    /// ```
    pub fn new() -> Result<Arc<Self>, DynError> {
        // allocate context
        let mut context = rcl::MTSafeFn::rcl_get_zero_initialized_context();

        // convert Args to Vec<*const c_ptr>
        let cstr_args: Vec<_> = env::args().map(|s| CString::new(s).unwrap()).collect();
        let args: Vec<_> = cstr_args.iter().map(|s| s.as_ptr()).collect();

        let options = InitOptions::new()?;

        {
            let guard = rcl::MT_UNSAFE_FN.lock();

            // initialize context
            guard.rcl_init(
                args.len() as i32,
                args.as_ptr(),
                options.as_ptr(),
                &mut context,
            )?;
        }

        let id;
        {
            let mut guard = ID_CONTEXT.lock();
            let mut n = 0;
            loop {
                if !guard.contains(&n) {
                    id = n;
                    guard.insert(n);
                    break;
                }
                n += 1;
            }
        }

        Ok(Arc::new(Context { context, id }))
    }

    /// Create a new node of ROS2.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::context::Context;
    ///
    /// // Create a context.
    /// let ctx = Context::new().unwrap();
    ///
    /// // Create a node.
    /// let node = ctx
    ///     .create_node("context_rs", None, Default::default())
    ///     .unwrap();
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::AlreadyInit` if the node has already be initialized, or
    /// - `RCLError::NotInit` if the given context is invalid, or
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::NodeInvalidName` if the name is invalid, or
    /// - `RCLError::NodeInvalidNamespace` if the namespace_ is invalid, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn create_node(
        self: &Arc<Self>,
        name: &str,
        namespace: Option<&str>,
        options: NodeOptions,
    ) -> RCLResult<Arc<Node>> {
        Node::new(self.clone(), name, namespace, options)
    }

    /// Create a new selector.
    /// The selector is used to wait event and invoke callback for single threaded execution.
    ///
    /// # Example
    ///
    /// ```
    /// use safe_drive::context::Context;
    ///
    /// // Create a context.
    /// let ctx = Context::new().unwrap();
    ///
    /// // Create a selector.
    /// let selector = ctx.create_selector().unwrap();
    /// ```
    ///
    /// # Errors
    ///
    /// - `RCLError::AlreadyInit` if the wait set is not zero initialized, or
    /// - `RCLError::NotInit` if the given context is invalid, or
    /// - `RCLError::InvalidArgument` if any arguments are invalid, or
    /// - `RCLError::BadAlloc` if allocating memory failed, or
    /// - `RCLError::WaitSetInvalid` if the wait set is not destroyed properly, or
    /// - `RCLError::Error` if an unspecified error occurs.
    pub fn create_selector(self: &Arc<Self>) -> RCLResult<Selector> {
        Selector::new(self.clone())
    }

    pub(crate) fn as_ptr(&self) -> *const rcl::rcl_context_t {
        &self.context as *const _
    }

    pub(crate) unsafe fn as_ptr_mut(&self) -> *mut rcl::rcl_context_t {
        &self.context as *const _ as *mut _
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        {
            let mut guard = ID_CONTEXT.lock();
            guard.remove(&self.id);
            if guard.is_empty() {
                SELECTOR.lock().halt(self).unwrap();
                signal_handler::halt();
            }
        };

        rcl::MTSafeFn::rcl_shutdown(&mut self.context).unwrap();
        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_context_fini(&mut self.context).unwrap();
        }
    }
}

/// Options for the initialization of the context.
pub(crate) struct InitOptions {
    options: rcl::rcl_init_options_t,
}

impl InitOptions {
    /// Create options to initialize a context.
    pub fn new() -> RCLResult<InitOptions> {
        // allocate options
        let mut options = rcl::MTSafeFn::rcl_get_zero_initialized_init_options();

        // initialize options
        {
            let guard = rcl::MT_UNSAFE_FN.lock();
            guard.rcl_init_options_init(
                &mut options,
                rcl::MTSafeFn::rcutils_get_default_allocator(),
            )?;
        }

        Ok(InitOptions { options })
    }

    pub fn as_ptr(&self) -> *const rcl::rcl_init_options_t {
        &self.options
    }

    pub fn as_ptr_mut(&mut self) -> *mut rcl::rcl_init_options_t {
        &mut self.options
    }
}

impl Drop for InitOptions {
    fn drop(&mut self) {
        let guard = rcl::MT_UNSAFE_FN.lock();
        guard.rcl_init_options_fini(self.as_ptr_mut()).unwrap();
    }
}

unsafe impl Sync for Context {}
unsafe impl Send for Context {}
