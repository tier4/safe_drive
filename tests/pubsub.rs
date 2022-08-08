pub mod common;

use safe_drive::{self, context::Context, msg::common_interfaces::std_msgs};
use std::error::Error;

const TOPIC_NAME: &str = "test_pubsub";

#[test]
fn test_pubsub() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = Context::new()?;

    // create a publish node
    let node_pub = ctx.create_node("test_pubusub_pub_node", None, Default::default())?;

    // create a subscribe node
    let node_sub = ctx.create_node("test_pubusub_sub_node", None, Default::default())?;

    // create a publisher and a subscriber
    let publisher = common::create_publisher(node_pub, TOPIC_NAME)?;
    let subscriber = common::create_subscriber(node_sub, TOPIC_NAME)?;

    // publish a message
    let n = 100;
    let msg = common::num::example_msg__msg__Num { num: n };
    publisher.send(&msg)?; // send message

    // wait messages
    let mut selector = ctx.create_selector()?;
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            assert_eq!(msg.num, n);
        }),
    );
    selector.wait()?;

    Ok(())
}

const PUBSUB_MSG: &str = "Hello, World!";

#[test]
fn test_pubsub_string() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = Context::new()?;

    // create a publish node
    let node_pub = ctx.create_node("test_pubusub_string_pub_node", None, Default::default())?;

    // create a subscribe node
    let node_sub = ctx.create_node("test_pubusub_string_sub_node", None, Default::default())?;

    // create a publisher and a subscriber
    let publisher =
        node_pub.create_publisher::<std_msgs::msg::String>("test_pubsub_string", None)?;
    let subscriber =
        node_sub.create_subscriber::<std_msgs::msg::String>("test_pubsub_string", None)?;

    // publish a message
    let mut msg = std_msgs::msg::String::new().unwrap();
    msg.data.assign(PUBSUB_MSG);
    publisher.send(&msg)?; // send message

    // wait messages
    let mut selector = ctx.create_selector()?;
    selector.add_subscriber(
        subscriber,
        Box::new(|msg| {
            let s = msg.data.to_string();
            println!("{s}");
            assert_eq!(&s, PUBSUB_MSG);
        }),
    );
    selector.wait()?;

    Ok(())
}
