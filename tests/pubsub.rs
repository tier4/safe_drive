pub mod common;

use safe_drive::{self, selector::Selector};
use std::error::Error;

const TOPIC_NAME: &str = "test_pubsub";

#[test]
fn test_pubsub() -> Result<(), Box<dyn Error>> {
    // create a context
    let ctx = safe_drive::context::Context::new()?;

    // create a publish node
    let node_pub = safe_drive::node::Node::new(
        ctx.clone(),
        "test_pubusub_pub_node",
        None,
        Default::default(),
    )?;

    // create a subscribe node
    let node_sub = safe_drive::node::Node::new(
        ctx.clone(),
        "test_pubusub_sub_node",
        None,
        Default::default(),
    )?;

    // create a publisher and a subscriber
    let publisher = common::create_publisher(node_pub, TOPIC_NAME)?;
    let subscriber = common::create_subscriber(node_sub, TOPIC_NAME)?;

    // publish a message
    let n = 100;
    let msg = common::num::sample_msg__msg__Num { num: n };
    publisher.send(msg)?; // send message

    // wait messages
    let mut selector = Selector::new(ctx)?;
    selector.add_subscriber(&subscriber, Box::new(|| ()));
    selector.wait(None)?;

    // receive the message
    match subscriber.try_recv() {
        Ok(msg) => {
            assert_eq!(msg.num, n);
            Ok(())
        }
        _ => panic!(),
    }
}
