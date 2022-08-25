#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(deref_nullptr)]
#![allow(non_snake_case)]
#![allow(improper_ctypes)]
#![allow(unused_imports)]
#![allow(clippy::upper_case_acronyms)]

pub mod msgs;

use msgs::example_msg::{msg::Num, srv::AddThreeInts};

use safe_drive::{
    self,
    error::{DynError, RCLResult},
    msg::{ServiceMsg, TopicMsg},
    node::Node,
    rcl,
    service::{client::Client, server::Server},
    topic::{publisher::Publisher, subscriber::Subscriber},
};
use std::{error::Error, sync::Arc};

pub fn create_publisher(node: Arc<Node>, topic_name: &str) -> RCLResult<Publisher<Num>> {
    node.create_publisher(topic_name, Default::default())
}

pub fn create_subscriber(node: Arc<Node>, topic_name: &str) -> RCLResult<Subscriber<Num>> {
    node.create_subscriber(topic_name, Default::default())
}

pub fn create_server(node: Arc<Node>, service_name: &str) -> RCLResult<Server<AddThreeInts>> {
    node.create_server(service_name, None)
}

pub fn create_client(node: Arc<Node>, service_name: &str) -> RCLResult<Client<AddThreeInts>> {
    node.create_client(service_name, None)
}
