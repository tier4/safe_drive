pub mod common;

use safe_drive::{self, context::Context, error::RCLError};
use std::error::Error;

#[test]
fn test_subscription() -> Result<(), Box<dyn Error>> {
    let ctx = Context::new()?;
    let node = ctx
        .create_node("test_subscription_node", None, Default::default())
        .unwrap();
    let subscription = node.create_subscriber::<common::num::example_msg__msg__Num>(
        "test_subscription",
        Default::default(),
    )?;

    match subscription.try_recv() {
        Err(RCLError::SubscriptionTakeFailed) => Ok(()), // must fail because there is no publisher
        _ => panic!(),
    }
}
