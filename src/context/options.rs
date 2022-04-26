use crate::{error::*, rcl};

/// Options for the initialization of a context
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
