pub mod common;

use safe_drive::{self, publisher::Publisher, subscriber::Subscriber};
use std::{
    error::Error,
    sync::{Arc, Mutex},
};

const NODE_NAME: &str = "test_pubsub_node";
const TOPIC_NAME: &str = "test_pubsub";

#[test]
fn test_pubsub() -> Result<(), Box<dyn Error>> {
    // create a publisher and a subscriber
    let publisher = create_publisher()?;
    let subscriber = create_subscriber()?;

    let n = 100;
    let msg = common::num::sample_msg__msg__Num { num: n };
    publisher.send(msg)?; // send message

    // receive message
    match subscriber.recv() {
        Ok(msg) => {
            assert_eq!(msg.num, n);
            Ok(())
        }
        _ => panic!(),
    }
}

fn create_publisher() -> Result<Publisher<common::num::sample_msg__msg__Num>, Box<dyn Error>> {
    let ctx = safe_drive::context::Context::new()?;
    let node = safe_drive::node::Node::new(ctx, NODE_NAME, None, Default::default()).unwrap();
    let publisher = safe_drive::publisher::Publisher::<common::num::sample_msg__msg__Num>::new(
        Arc::new(Mutex::new(node)),
        TOPIC_NAME,
        unsafe {
            common::num::rosidl_typesupport_c__get_message_type_support_handle__sample_msg__msg__Num(
            ) as *const ()
        },
        Default::default(),
    )?;

    Ok(publisher)
}

fn create_subscriber() -> Result<Subscriber<common::num::sample_msg__msg__Num>, Box<dyn Error>> {
    let ctx = safe_drive::context::Context::new()?;
    let node = safe_drive::node::Node::new(ctx, NODE_NAME, None, Default::default()).unwrap();
    let subscriber = safe_drive::subscriber::Subscriber::<common::num::sample_msg__msg__Num>::new(
        Arc::new(Mutex::new(node)),
        TOPIC_NAME,
        unsafe {
            common::num::rosidl_typesupport_c__get_message_type_support_handle__sample_msg__msg__Num(
            ) as *const ()
        },
        Default::default(),
    )?;

    Ok(subscriber)
}
