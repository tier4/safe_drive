#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(clippy::upper_case_acronyms)]

pub mod add_three_ints;
pub mod num;

use safe_drive::{self, node::Node, publisher::Publisher, subscriber::Subscriber};
use std::{error::Error, sync::Arc};

pub fn create_publisher(
    node: Arc<Node>,
    topic_name: &str,
) -> Result<Publisher<num::sample_msg__msg__Num>, Box<dyn Error>> {
    let publisher = node.create_publisher::<num::sample_msg__msg__Num>(
        topic_name,
        unsafe {
            num::rosidl_typesupport_c__get_message_type_support_handle__sample_msg__msg__Num()
                as *const ()
        },
        Default::default(),
    )?;

    Ok(publisher)
}

pub fn create_subscriber(
    node: Arc<Node>,
    topic_name: &str,
) -> Result<Subscriber<num::sample_msg__msg__Num>, Box<dyn Error>> {
    let subscriber = node.create_subscriber::<num::sample_msg__msg__Num>(
        topic_name,
        unsafe {
            num::rosidl_typesupport_c__get_message_type_support_handle__sample_msg__msg__Num()
                as *const ()
        },
        Default::default(),
    )?;

    Ok(subscriber)
}
