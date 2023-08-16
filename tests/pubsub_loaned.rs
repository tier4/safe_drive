pub mod common;

use common::msgs::example_msg::msg::Num;
use safe_drive::{self, context::Context};
use std::error::Error;

const TOPIC_NAME: &str = "test_pubsub_loaned";

#[test]
fn test_pubsub_loaned() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    // create a context
    let ctx = Context::new()?;

    // create a publish node
    let node_pub = ctx.create_node("test_pubsub_loaned_pub_node", None, Default::default())?;

    // create a subscribe node
    let node_sub = ctx.create_node("test_pubsub_loaned_sub_node", None, Default::default())?;

    // create a publisher and a subscriber
    let publisher = common::create_publisher(node_pub, TOPIC_NAME, false)?;
    let subscriber = common::create_subscriber(node_sub, TOPIC_NAME, false)?;

    // publish a message
    let num = 100;

    let mut loaned = publisher.borrow_loaned_message()?;
    *loaned = Num { num };
    publisher.send_loaned(loaned)?; // send message

    // wait messages
    let mut selector = ctx.create_selector()?;
    selector.add_subscriber(
        subscriber,
        Box::new(move |msg| {
            assert_eq!(msg.num, num);
        }),
    );
    selector.wait()?;

    Ok(())
}
