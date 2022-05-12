pub mod common;

use safe_drive::{self, error::RCLError};
use std::{
    error::Error,
    sync::{Arc, Mutex},
};

#[test]
fn test_subscription() -> Result<(), Box<dyn Error>> {
    let ctx = safe_drive::context::Context::new()?;
    let node =
        safe_drive::node::Node::new(ctx, "test_create_node", None, Default::default()).unwrap();
    let subscription =
        safe_drive::subscriber::Subscriber::<common::num::sample_msg__msg__Num>::new(
            Arc::new(Mutex::new(node)),
            "test_subscription",
            unsafe {
                common::num::rosidl_typesupport_c__get_message_type_support_handle__sample_msg__msg__Num(
            ) as *const ()
            },
            Default::default(),
        )?;

    match subscription.recv() {
        Err(RCLError::SubscriptionTakeFailed) => Ok(()), // must fail because there is no publisher
        _ => panic!(),
    }
}
