#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(unused_imports)]
#![allow(clippy::upper_case_acronyms)]

pub mod add_three_ints;
pub mod num;

use safe_drive::{
    self,
    msg::TopicMsg,
    node::Node,
    rcl,
    service::{client::Client, server::Server},
    topic::{publisher::Publisher, subscriber::Subscriber},
};
use std::{error::Error, sync::Arc};

impl TopicMsg for num::example_msg__msg__Num {
    fn type_support() -> *const rcl::rosidl_message_type_support_t {
        unsafe {
            num::rosidl_typesupport_c__get_message_type_support_handle__example_msg__msg__Num()
        }
    }
}

pub fn create_publisher(
    node: Arc<Node>,
    topic_name: &str,
) -> Result<Publisher<num::example_msg__msg__Num>, Box<dyn Error>> {
    let publisher =
        node.create_publisher::<num::example_msg__msg__Num>(topic_name, Default::default())?;

    Ok(publisher)
}

pub fn create_subscriber(
    node: Arc<Node>,
    topic_name: &str,
) -> Result<Subscriber<num::example_msg__msg__Num>, Box<dyn Error>> {
    let subscriber =
        node.create_subscriber::<num::example_msg__msg__Num>(topic_name, Default::default())?;

    Ok(subscriber)
}

pub type Request = add_three_ints::example_msg__srv__AddThreeInts_Request;
pub type Response = add_three_ints::example_msg__srv__AddThreeInts_Response;

pub type ServerType = Server<Request, Response>;
pub type ClientType = Client<Request, Response>;

pub fn create_server(node: Arc<Node>, service_name: &str) -> Result<ServerType, Box<dyn Error>> {
    let server = node.create_server(
        service_name,
        unsafe { add_three_ints::rosidl_typesupport_c__get_service_type_support_handle__example_msg__srv__AddThreeInts() as *const()},
        None,
    )?;

    Ok(server)
}

pub fn create_client(node: Arc<Node>, service_name: &str) -> Result<ClientType, Box<dyn Error>> {
    let client = node.create_client(
        service_name,
        unsafe { add_three_ints::rosidl_typesupport_c__get_service_type_support_handle__example_msg__srv__AddThreeInts() as *const()},
        None,
    )?;

    Ok(client)
}
