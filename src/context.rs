use crate::{error::*, rcl};
use std::{
    env,
    ffi::CString,
    sync::{Arc, Mutex},
};

pub struct Context {
    context: rcl::rcl_context_t,
}

impl Context {
    pub fn new() -> RCLResult<Arc<Mutex<Self>>> {
        // allocate context
        let mut context = unsafe { rcl::rcl_get_zero_initialized_context() };

        // convert Args to Vec<*const c_ptr>
        let cstr_args: Vec<_> = env::args().map(|s| CString::new(s).unwrap()).collect();
        let args: Vec<_> = cstr_args.iter().map(|s| s.as_ptr()).collect();

        let options = InitOptions::new()?;

        // initialize context
        ret_val_to_err(unsafe {
            rcl::rcl_init(
                args.len() as i32,
                args.as_ptr(),
                options.as_ptr(),
                &mut context,
            )
        })?;

        Ok(Arc::new(Mutex::new(Context { context })))
    }

    pub(crate) fn as_ptr_mut(&mut self) -> *mut rcl::rcl_context_t {
        &mut self.context
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        ret_val_to_err(unsafe { rcl::rcl_shutdown(&mut self.context) }).unwrap();
        ret_val_to_err(unsafe { rcl::rcl_context_fini(&mut self.context) }).unwrap();
    }
}

/// Options for the initialization of the context.
pub struct InitOptions {
    options: rcl::rcl_init_options_t,
}

impl InitOptions {
    /// Create options to initialize a context.
    pub fn new() -> RCLResult<InitOptions> {
        // allocate options
        let mut options = unsafe { rcl::rcl_get_zero_initialized_init_options() };

        // initialize options
        ret_val_to_err(unsafe {
            rcl::rcl_init_options_init(&mut options, rcl::rcutils_get_default_allocator())
        })?;

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
        ret_val_to_err(unsafe { rcl::rcl_init_options_fini(self.as_ptr_mut()) }).unwrap();
    }
}
