use std::{env, ffi::CString};

use crate::{error::*, init_options::InitOptions, rcl};

pub struct Context {
    context: rcl::rcl_context_t,
}

impl Context {
    pub fn new() -> RCLResult<Context> {
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

        Ok(Context { context })
    }
}


