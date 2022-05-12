#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(clippy::upper_case_acronyms)]

mod galactic;

pub use galactic::*;

use crate::error::{ret_val_to_err, RCLResult};
use once_cell::sync::Lazy;
use std::{marker::PhantomData, sync::Mutex};

pub static MT_UNSAFE_FN: Lazy<Mutex<MTUnsafeFn>> = Lazy::new(|| Mutex::new(MTUnsafeFn::new()));

pub struct MTUnsafeFn {
    _phantom: PhantomData<usize>,
}

impl MTUnsafeFn {
    fn new() -> Self {
        MTUnsafeFn {
            _phantom: Default::default(),
        }
    }

    pub fn rcl_init(
        &self,
        argc: ::std::os::raw::c_int,
        argv: *const *const ::std::os::raw::c_char,
        options: *const rcl_init_options_t,
        context: *mut rcl_context_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_init(argc, argv, options, context) })
    }

    pub fn rcl_context_fini(&self, context: *mut rcl_context_t) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_context_fini(context) })
    }

    pub fn rcl_init_options_init(
        &self,
        init_options: *mut rcl_init_options_t,
        allocator: rcl_allocator_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_init_options_init(init_options, allocator) })
    }

    pub fn rcl_init_options_fini(&self, init_options: *mut rcl_init_options_t) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_init_options_fini(init_options) })
    }

    pub fn rcl_node_init(
        &self,
        node: *mut rcl_node_t,
        name: *const ::std::os::raw::c_char,
        namespace_: *const ::std::os::raw::c_char,
        context: *mut rcl_context_t,
        options: *const rcl_node_options_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe {
            crate::rcl::rcl_node_init(node, name, namespace_, context, options)
        })
    }

    pub fn rcl_node_fini(&self, node: *mut rcl_node_t) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_node_fini(node) })
    }

    pub fn rcl_node_options_fini(&self, options: *mut rcl_node_options_t) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_node_options_fini(options) })
    }

    pub fn rcl_publisher_init(
        &self,
        publisher: *mut rcl_publisher_t,
        node: *const rcl_node_t,
        type_support: *const rosidl_message_type_support_t,
        topic_name: *const ::std::os::raw::c_char,
        options: *const rcl_publisher_options_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe {
            crate::rcl::rcl_publisher_init(publisher, node, type_support, topic_name, options)
        })
    }

    pub fn rcl_publisher_fini(
        &self,
        publisher: *mut rcl_publisher_t,
        node: *mut rcl_node_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_publisher_fini(publisher, node) })
    }

    pub fn rcl_subscription_fini(
        &self,
        subscription: *mut rcl_subscription_t,
        node: *mut rcl_node_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_subscription_fini(subscription, node) })
    }

    pub fn rcl_subscription_init(
        &self,
        subscription: *mut rcl_subscription_t,
        node: *const rcl_node_t,
        type_support: *const rosidl_message_type_support_t,
        topic_name: *const ::std::os::raw::c_char,
        options: *const rcl_subscription_options_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe {
            crate::rcl::rcl_subscription_init(subscription, node, type_support, topic_name, options)
        })
    }

    pub fn rcl_take(
        &self,
        subscription: *const rcl_subscription_t,
        ros_message: *mut ::std::os::raw::c_void,
        message_info: *mut rmw_message_info_t,
        allocation: *mut rmw_subscription_allocation_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe {
            crate::rcl::rcl_take(subscription, ros_message, message_info, allocation)
        })
    }
}

pub struct MTSafeFn {
    _phantom: PhantomData<usize>,
}

impl MTSafeFn {
    pub fn rcl_get_zero_initialized_context() -> rcl_context_t {
        unsafe { crate::rcl::rcl_get_zero_initialized_context() }
    }

    pub fn rcl_shutdown(context: *mut rcl_context_t) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_shutdown(context) })
    }

    pub fn rcutils_get_default_allocator() -> rcutils_allocator_t {
        unsafe { crate::rcl::rcutils_get_default_allocator() }
    }

    pub fn rcl_get_zero_initialized_init_options() -> rcl_init_options_t {
        unsafe { crate::rcl::rcl_get_zero_initialized_init_options() }
    }

    pub fn rcl_get_zero_initialized_node() -> rcl_node_t {
        unsafe { crate::rcl::rcl_get_zero_initialized_node() }
    }

    pub fn rcl_node_get_default_options() -> rcl_node_options_t {
        unsafe { crate::rcl::rcl_node_get_default_options() }
    }

    pub fn rcl_get_zero_initialized_publisher() -> rcl_publisher_t {
        unsafe { crate::rcl::rcl_get_zero_initialized_publisher() }
    }

    pub fn rcl_publish(
        publisher: *const rcl_publisher_t,
        ros_message: *const ::std::os::raw::c_void,
        allocation: *mut rmw_publisher_allocation_t,
    ) -> RCLResult<()> {
        ret_val_to_err(unsafe { crate::rcl::rcl_publish(publisher, ros_message, allocation) })
    }

    pub fn rmw_get_default_publisher_options() -> rmw_publisher_options_t {
        unsafe { crate::rcl::rmw_get_default_publisher_options() }
    }

    pub fn rcl_get_zero_initialized_subscription() -> rcl_subscription_t {
        unsafe { crate::rcl::rcl_get_zero_initialized_subscription() }
    }

    pub fn rmw_get_default_subscription_options() -> rmw_subscription_options_t {
        unsafe { crate::rcl::rmw_get_default_subscription_options() }
    }
}
