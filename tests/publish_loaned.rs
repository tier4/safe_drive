pub mod common;

use common::msgs::example_msg::msg::Num;
use safe_drive::{self, context::Context};
use std::error::Error;

const TOPIC_NAME: &str = "test_publish_loaned";

#[test]
fn test_publish_loaned() -> Result<(), Box<dyn Error + Sync + Send + 'static>> {
    let ctx = Context::new()?;
    let node = ctx
        .create_node("test_publish_node", None, Default::default())
        .unwrap();

    let publisher = node.create_publisher::<Num>(TOPIC_NAME, Default::default())?;

    let mut loaned = publisher.borrow_loaned_message()?;
    *loaned = Num { num: 100 };

    publisher.send_loaned(loaned)?;

    Ok(())
}
